%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:04 EST 2020

% Result     : Theorem 6.03s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 313 expanded)
%              Number of leaves         :   27 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 (1183 expanded)
%              Number of equality atoms :   38 (  91 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v1_tops_1(B,A)
                & v2_tex_2(B,A) )
             => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_40,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_781,plain,(
    ! [A_116,B_117] :
      ( '#skF_1'(A_116,B_117) != B_117
      | v3_tex_2(B_117,A_116)
      | ~ v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_794,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_781])).

tff(c_803,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_794])).

tff(c_804,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_803])).

tff(c_870,plain,(
    ! [A_125,B_126] :
      ( v2_tex_2('#skF_1'(A_125,B_126),A_125)
      | v3_tex_2(B_126,A_125)
      | ~ v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_879,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_870])).

tff(c_888,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_879])).

tff(c_889,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_888])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_805,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(B_118,'#skF_1'(A_119,B_118))
      | v3_tex_2(B_118,A_119)
      | ~ v2_tex_2(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_814,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_805])).

tff(c_823,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_814])).

tff(c_824,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_823])).

tff(c_26,plain,(
    ! [A_17,B_23] :
      ( m1_subset_1('#skF_1'(A_17,B_23),k1_zfmisc_1(u1_struct_0(A_17)))
      | v3_tex_2(B_23,A_17)
      | ~ v2_tex_2(B_23,A_17)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_959,plain,(
    ! [A_133,B_134] :
      ( m1_subset_1('#skF_1'(A_133,B_134),k1_zfmisc_1(u1_struct_0(A_133)))
      | v3_tex_2(B_134,A_133)
      | ~ v2_tex_2(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [B_16,A_14] :
      ( v1_tops_1(B_16,A_14)
      | k2_pre_topc(A_14,B_16) != u1_struct_0(A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3553,plain,(
    ! [A_222,B_223] :
      ( v1_tops_1('#skF_1'(A_222,B_223),A_222)
      | k2_pre_topc(A_222,'#skF_1'(A_222,B_223)) != u1_struct_0(A_222)
      | v3_tex_2(B_223,A_222)
      | ~ v2_tex_2(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_959,c_16])).

tff(c_3566,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) != u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_3553])).

tff(c_3577,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) != u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_3566])).

tff(c_3578,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) != u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3577])).

tff(c_3579,plain,(
    k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3578])).

tff(c_44,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_118,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,B_55) = u1_struct_0(A_54)
      | ~ v1_tops_1(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_128,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_118])).

tff(c_133,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_128])).

tff(c_1160,plain,(
    ! [A_152,B_153,C_154] :
      ( r1_tarski(k2_pre_topc(A_152,B_153),k2_pre_topc(A_152,C_154))
      | ~ r1_tarski(B_153,C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1171,plain,(
    ! [C_154] :
      ( r1_tarski(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3',C_154))
      | ~ r1_tarski('#skF_4',C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1160])).

tff(c_1218,plain,(
    ! [C_158] :
      ( r1_tarski(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3',C_158))
      | ~ r1_tarski('#skF_4',C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1171])).

tff(c_88,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k2_pre_topc(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k2_pre_topc(A_52,B_53),u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_88,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,B_53) = u1_struct_0(A_52)
      | ~ r1_tarski(u1_struct_0(A_52),k2_pre_topc(A_52,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_1223,plain,(
    ! [C_158] :
      ( k2_pre_topc('#skF_3',C_158) = u1_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski('#skF_4',C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1218,c_117])).

tff(c_1241,plain,(
    ! [C_159] :
      ( k2_pre_topc('#skF_3',C_159) = u1_struct_0('#skF_3')
      | ~ r1_tarski('#skF_4',C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1223])).

tff(c_1249,plain,(
    ! [B_23] :
      ( k2_pre_topc('#skF_3','#skF_1'('#skF_3',B_23)) = u1_struct_0('#skF_3')
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_23))
      | v3_tex_2(B_23,'#skF_3')
      | ~ v2_tex_2(B_23,'#skF_3')
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_1241])).

tff(c_3999,plain,(
    ! [B_236] :
      ( k2_pre_topc('#skF_3','#skF_1'('#skF_3',B_236)) = u1_struct_0('#skF_3')
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_236))
      | v3_tex_2(B_236,'#skF_3')
      | ~ v2_tex_2(B_236,'#skF_3')
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1249])).

tff(c_4021,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_3999])).

tff(c_4037,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_824,c_4021])).

tff(c_4039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3579,c_4037])).

tff(c_4041,plain,(
    k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3578])).

tff(c_14,plain,(
    ! [A_7,B_11,C_13] :
      ( r1_tarski(k2_pre_topc(A_7,B_11),k2_pre_topc(A_7,C_13))
      | ~ r1_tarski(B_11,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4107,plain,(
    ! [B_11] :
      ( r1_tarski(k2_pre_topc('#skF_3',B_11),u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_11,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4041,c_14])).

tff(c_4168,plain,(
    ! [B_11] :
      ( r1_tarski(k2_pre_topc('#skF_3',B_11),u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_11,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4107])).

tff(c_4586,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4168])).

tff(c_4589,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_4586])).

tff(c_4595,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_4589])).

tff(c_4597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4595])).

tff(c_4599,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4168])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1672,plain,(
    ! [A_174,B_175,C_176] :
      ( k9_subset_1(u1_struct_0(A_174),B_175,k2_pre_topc(A_174,C_176)) = C_176
      | ~ r1_tarski(C_176,B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ v2_tex_2(B_175,A_174)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1685,plain,(
    ! [B_175] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_175,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_175)
      | ~ v2_tex_2(B_175,'#skF_3')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_1672])).

tff(c_1696,plain,(
    ! [B_175] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_175,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_175)
      | ~ v2_tex_2(B_175,'#skF_3')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_133,c_1685])).

tff(c_1697,plain,(
    ! [B_175] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_175,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_175)
      | ~ v2_tex_2(B_175,'#skF_3')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1696])).

tff(c_4630,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4599,c_1697])).

tff(c_4708,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_824,c_4630])).

tff(c_32,plain,(
    ! [A_27,B_33,C_36] :
      ( k9_subset_1(u1_struct_0(A_27),B_33,k2_pre_topc(A_27,C_36)) = C_36
      | ~ r1_tarski(C_36,B_33)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v2_tex_2(B_33,A_27)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4638,plain,(
    ! [B_33] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_33,k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4'))) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_33)
      | ~ v2_tex_2(B_33,'#skF_3')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4599,c_32])).

tff(c_4716,plain,(
    ! [B_33] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_33,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_33)
      | ~ v2_tex_2(B_33,'#skF_3')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4041,c_4638])).

tff(c_4838,plain,(
    ! [B_247] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_247,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_247)
      | ~ v2_tex_2(B_247,'#skF_3')
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4716])).

tff(c_4841,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4599,c_4838])).

tff(c_4866,plain,(
    '#skF_1'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_6,c_4708,c_4841])).

tff(c_4868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_804,c_4866])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.03/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.24  
% 6.03/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.25  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.03/2.25  
% 6.03/2.25  %Foreground sorts:
% 6.03/2.25  
% 6.03/2.25  
% 6.03/2.25  %Background operators:
% 6.03/2.25  
% 6.03/2.25  
% 6.03/2.25  %Foreground operators:
% 6.03/2.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.03/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.03/2.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.03/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.03/2.25  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 6.03/2.25  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.03/2.25  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.03/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.03/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.03/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.03/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.03/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.03/2.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.03/2.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.03/2.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.03/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.03/2.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.03/2.25  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.03/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.03/2.25  
% 6.03/2.26  tff(f_116, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 6.03/2.26  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 6.03/2.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.03/2.26  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 6.03/2.26  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 6.03/2.26  tff(f_41, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.03/2.26  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.03/2.26  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 6.03/2.26  tff(c_40, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.03/2.26  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.03/2.26  tff(c_42, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.03/2.26  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.03/2.26  tff(c_781, plain, (![A_116, B_117]: ('#skF_1'(A_116, B_117)!=B_117 | v3_tex_2(B_117, A_116) | ~v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.03/2.26  tff(c_794, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_781])).
% 6.03/2.26  tff(c_803, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_794])).
% 6.03/2.26  tff(c_804, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_40, c_803])).
% 6.03/2.26  tff(c_870, plain, (![A_125, B_126]: (v2_tex_2('#skF_1'(A_125, B_126), A_125) | v3_tex_2(B_126, A_125) | ~v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.03/2.26  tff(c_879, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_870])).
% 6.03/2.26  tff(c_888, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_879])).
% 6.03/2.26  tff(c_889, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_888])).
% 6.03/2.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.03/2.26  tff(c_805, plain, (![B_118, A_119]: (r1_tarski(B_118, '#skF_1'(A_119, B_118)) | v3_tex_2(B_118, A_119) | ~v2_tex_2(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.03/2.26  tff(c_814, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_805])).
% 6.03/2.26  tff(c_823, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_814])).
% 6.03/2.26  tff(c_824, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_823])).
% 6.03/2.26  tff(c_26, plain, (![A_17, B_23]: (m1_subset_1('#skF_1'(A_17, B_23), k1_zfmisc_1(u1_struct_0(A_17))) | v3_tex_2(B_23, A_17) | ~v2_tex_2(B_23, A_17) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.03/2.27  tff(c_959, plain, (![A_133, B_134]: (m1_subset_1('#skF_1'(A_133, B_134), k1_zfmisc_1(u1_struct_0(A_133))) | v3_tex_2(B_134, A_133) | ~v2_tex_2(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.03/2.27  tff(c_16, plain, (![B_16, A_14]: (v1_tops_1(B_16, A_14) | k2_pre_topc(A_14, B_16)!=u1_struct_0(A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.03/2.27  tff(c_3553, plain, (![A_222, B_223]: (v1_tops_1('#skF_1'(A_222, B_223), A_222) | k2_pre_topc(A_222, '#skF_1'(A_222, B_223))!=u1_struct_0(A_222) | v3_tex_2(B_223, A_222) | ~v2_tex_2(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(resolution, [status(thm)], [c_959, c_16])).
% 6.03/2.27  tff(c_3566, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_3553])).
% 6.03/2.27  tff(c_3577, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_3566])).
% 6.03/2.27  tff(c_3578, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_3577])).
% 6.03/2.27  tff(c_3579, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3578])).
% 6.03/2.27  tff(c_44, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.03/2.27  tff(c_118, plain, (![A_54, B_55]: (k2_pre_topc(A_54, B_55)=u1_struct_0(A_54) | ~v1_tops_1(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.03/2.27  tff(c_128, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_118])).
% 6.03/2.27  tff(c_133, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_128])).
% 6.03/2.27  tff(c_1160, plain, (![A_152, B_153, C_154]: (r1_tarski(k2_pre_topc(A_152, B_153), k2_pre_topc(A_152, C_154)) | ~r1_tarski(B_153, C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.03/2.27  tff(c_1171, plain, (![C_154]: (r1_tarski(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', C_154)) | ~r1_tarski('#skF_4', C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1160])).
% 6.03/2.27  tff(c_1218, plain, (![C_158]: (r1_tarski(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', C_158)) | ~r1_tarski('#skF_4', C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1171])).
% 6.03/2.27  tff(c_88, plain, (![A_47, B_48]: (m1_subset_1(k2_pre_topc(A_47, B_48), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.03/2.27  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.03/2.27  tff(c_110, plain, (![A_52, B_53]: (r1_tarski(k2_pre_topc(A_52, B_53), u1_struct_0(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_88, c_8])).
% 6.03/2.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.03/2.27  tff(c_117, plain, (![A_52, B_53]: (k2_pre_topc(A_52, B_53)=u1_struct_0(A_52) | ~r1_tarski(u1_struct_0(A_52), k2_pre_topc(A_52, B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_110, c_2])).
% 6.03/2.27  tff(c_1223, plain, (![C_158]: (k2_pre_topc('#skF_3', C_158)=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski('#skF_4', C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_1218, c_117])).
% 6.03/2.27  tff(c_1241, plain, (![C_159]: (k2_pre_topc('#skF_3', C_159)=u1_struct_0('#skF_3') | ~r1_tarski('#skF_4', C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1223])).
% 6.03/2.27  tff(c_1249, plain, (![B_23]: (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', B_23))=u1_struct_0('#skF_3') | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_23)) | v3_tex_2(B_23, '#skF_3') | ~v2_tex_2(B_23, '#skF_3') | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_1241])).
% 6.03/2.27  tff(c_3999, plain, (![B_236]: (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', B_236))=u1_struct_0('#skF_3') | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_236)) | v3_tex_2(B_236, '#skF_3') | ~v2_tex_2(B_236, '#skF_3') | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1249])).
% 6.03/2.27  tff(c_4021, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_3999])).
% 6.03/2.27  tff(c_4037, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_824, c_4021])).
% 6.03/2.27  tff(c_4039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_3579, c_4037])).
% 6.03/2.27  tff(c_4041, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_3578])).
% 6.03/2.27  tff(c_14, plain, (![A_7, B_11, C_13]: (r1_tarski(k2_pre_topc(A_7, B_11), k2_pre_topc(A_7, C_13)) | ~r1_tarski(B_11, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.03/2.27  tff(c_4107, plain, (![B_11]: (r1_tarski(k2_pre_topc('#skF_3', B_11), u1_struct_0('#skF_3')) | ~r1_tarski(B_11, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4041, c_14])).
% 6.03/2.27  tff(c_4168, plain, (![B_11]: (r1_tarski(k2_pre_topc('#skF_3', B_11), u1_struct_0('#skF_3')) | ~r1_tarski(B_11, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4107])).
% 6.03/2.27  tff(c_4586, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_4168])).
% 6.03/2.27  tff(c_4589, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_4586])).
% 6.03/2.27  tff(c_4595, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_4589])).
% 6.03/2.27  tff(c_4597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_4595])).
% 6.03/2.27  tff(c_4599, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_4168])).
% 6.03/2.27  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.03/2.27  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.03/2.27  tff(c_1672, plain, (![A_174, B_175, C_176]: (k9_subset_1(u1_struct_0(A_174), B_175, k2_pre_topc(A_174, C_176))=C_176 | ~r1_tarski(C_176, B_175) | ~m1_subset_1(C_176, k1_zfmisc_1(u1_struct_0(A_174))) | ~v2_tex_2(B_175, A_174) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.03/2.27  tff(c_1685, plain, (![B_175]: (k9_subset_1(u1_struct_0('#skF_3'), B_175, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_175) | ~v2_tex_2(B_175, '#skF_3') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_1672])).
% 6.03/2.27  tff(c_1696, plain, (![B_175]: (k9_subset_1(u1_struct_0('#skF_3'), B_175, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_175) | ~v2_tex_2(B_175, '#skF_3') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_133, c_1685])).
% 6.03/2.27  tff(c_1697, plain, (![B_175]: (k9_subset_1(u1_struct_0('#skF_3'), B_175, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_175) | ~v2_tex_2(B_175, '#skF_3') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_1696])).
% 6.03/2.27  tff(c_4630, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_4599, c_1697])).
% 6.03/2.27  tff(c_4708, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_889, c_824, c_4630])).
% 6.03/2.27  tff(c_32, plain, (![A_27, B_33, C_36]: (k9_subset_1(u1_struct_0(A_27), B_33, k2_pre_topc(A_27, C_36))=C_36 | ~r1_tarski(C_36, B_33) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_27))) | ~v2_tex_2(B_33, A_27) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.03/2.27  tff(c_4638, plain, (![B_33]: (k9_subset_1(u1_struct_0('#skF_3'), B_33, k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4')))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_33) | ~v2_tex_2(B_33, '#skF_3') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4599, c_32])).
% 6.03/2.27  tff(c_4716, plain, (![B_33]: (k9_subset_1(u1_struct_0('#skF_3'), B_33, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_33) | ~v2_tex_2(B_33, '#skF_3') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4041, c_4638])).
% 6.03/2.27  tff(c_4838, plain, (![B_247]: (k9_subset_1(u1_struct_0('#skF_3'), B_247, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_247) | ~v2_tex_2(B_247, '#skF_3') | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_4716])).
% 6.03/2.27  tff(c_4841, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_4599, c_4838])).
% 6.03/2.27  tff(c_4866, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_889, c_6, c_4708, c_4841])).
% 6.03/2.27  tff(c_4868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_804, c_4866])).
% 6.03/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.27  
% 6.03/2.27  Inference rules
% 6.03/2.27  ----------------------
% 6.03/2.27  #Ref     : 0
% 6.03/2.27  #Sup     : 969
% 6.03/2.27  #Fact    : 0
% 6.03/2.27  #Define  : 0
% 6.03/2.27  #Split   : 19
% 6.03/2.27  #Chain   : 0
% 6.03/2.27  #Close   : 0
% 6.03/2.27  
% 6.03/2.27  Ordering : KBO
% 6.03/2.27  
% 6.03/2.27  Simplification rules
% 6.03/2.27  ----------------------
% 6.03/2.27  #Subsume      : 146
% 6.03/2.27  #Demod        : 1387
% 6.03/2.27  #Tautology    : 416
% 6.03/2.27  #SimpNegUnit  : 116
% 6.03/2.27  #BackRed      : 0
% 6.03/2.27  
% 6.03/2.27  #Partial instantiations: 0
% 6.03/2.27  #Strategies tried      : 1
% 6.03/2.27  
% 6.03/2.27  Timing (in seconds)
% 6.03/2.27  ----------------------
% 6.03/2.27  Preprocessing        : 0.37
% 6.03/2.27  Parsing              : 0.19
% 6.03/2.27  CNF conversion       : 0.03
% 6.03/2.27  Main loop            : 1.05
% 6.03/2.27  Inferencing          : 0.32
% 6.03/2.27  Reduction            : 0.35
% 6.03/2.27  Demodulation         : 0.24
% 6.03/2.27  BG Simplification    : 0.04
% 6.03/2.27  Subsumption          : 0.28
% 6.03/2.27  Abstraction          : 0.06
% 6.03/2.27  MUC search           : 0.00
% 6.03/2.27  Cooper               : 0.00
% 6.03/2.27  Total                : 1.47
% 6.03/2.27  Index Insertion      : 0.00
% 6.03/2.27  Index Deletion       : 0.00
% 6.03/2.27  Index Matching       : 0.00
% 6.03/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
