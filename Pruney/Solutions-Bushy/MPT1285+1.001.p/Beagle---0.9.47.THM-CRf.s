%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1285+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:43 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 581 expanded)
%              Number of leaves         :   27 ( 209 expanded)
%              Depth                    :   13
%              Number of atoms          :  424 (2541 expanded)
%              Number of equality atoms :   42 ( 112 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(c_44,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1624,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_53,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1294,plain,(
    ! [B_168,A_169] :
      ( r1_tarski(B_168,k2_pre_topc(A_169,B_168))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1298,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1294])).

tff(c_1304,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1298])).

tff(c_657,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(B_113,k2_pre_topc(A_114,B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_661,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_657])).

tff(c_667,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_661])).

tff(c_64,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_104,plain,(
    ! [A_60,B_61] :
      ( k1_tops_1(A_60,k2_pre_topc(A_60,B_61)) = B_61
      | ~ v6_tops_1(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_114,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_108])).

tff(c_95,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k2_pre_topc(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v3_pre_topc(k1_tops_1(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_131,plain,(
    ! [A_64,B_65] :
      ( v3_pre_topc(k1_tops_1(A_64,k2_pre_topc(A_64,B_65)),A_64)
      | ~ v2_pre_topc(A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_95,c_20])).

tff(c_134,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_131])).

tff(c_136,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_134])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_136])).

tff(c_140,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_139,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_141,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_146,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,k2_pre_topc(A_67,B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_148,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_146])).

tff(c_153,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_148])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k2_pre_topc(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_184,plain,(
    ! [A_72,B_73] :
      ( k1_tops_1(A_72,k2_pre_topc(A_72,B_73)) = B_73
      | ~ v6_tops_1(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_188,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_184])).

tff(c_194,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_188])).

tff(c_236,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(k1_tops_1(A_84,B_85),k1_tops_1(A_84,C_86))
      | ~ r1_tarski(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_241,plain,(
    ! [C_86] :
      ( r1_tarski('#skF_3',k1_tops_1('#skF_1',C_86))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_236])).

tff(c_247,plain,(
    ! [C_86] :
      ( r1_tarski('#skF_3',k1_tops_1('#skF_1',C_86))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_241])).

tff(c_250,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_253,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_250])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_253])).

tff(c_259,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_28,plain,(
    ! [B_31,D_37,C_35,A_23] :
      ( k1_tops_1(B_31,D_37) = D_37
      | ~ v3_pre_topc(D_37,B_31)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0(B_31)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_364,plain,(
    ! [C_93,A_94] :
      ( ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_367,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_259,c_364])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_367])).

tff(c_391,plain,(
    ! [B_96,D_97] :
      ( k1_tops_1(B_96,D_97) = D_97
      | ~ v3_pre_topc(D_97,B_96)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(u1_struct_0(B_96)))
      | ~ l1_pre_topc(B_96) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_400,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_391])).

tff(c_411,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_140,c_400])).

tff(c_244,plain,(
    ! [B_85] :
      ( r1_tarski(k1_tops_1('#skF_1',B_85),'#skF_3')
      | ~ r1_tarski(B_85,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_236])).

tff(c_249,plain,(
    ! [B_85] :
      ( r1_tarski(k1_tops_1('#skF_1',B_85),'#skF_3')
      | ~ r1_tarski(B_85,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_244])).

tff(c_315,plain,(
    ! [B_90] :
      ( r1_tarski(k1_tops_1('#skF_1',B_90),'#skF_3')
      | ~ r1_tarski(B_90,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_249])).

tff(c_325,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_315])).

tff(c_334,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_325])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_337,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_338,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_415,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_338])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_415])).

tff(c_421,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_322,plain,(
    ! [B_10] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',B_10)),'#skF_3')
      | ~ r1_tarski(k2_pre_topc('#skF_1',B_10),k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_315])).

tff(c_331,plain,(
    ! [B_10] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',B_10)),'#skF_3')
      | ~ r1_tarski(k2_pre_topc('#skF_1',B_10),k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_322])).

tff(c_623,plain,(
    ! [B_111,A_112] :
      ( v4_tops_1(B_111,A_112)
      | ~ r1_tarski(B_111,k2_pre_topc(A_112,k1_tops_1(A_112,B_111)))
      | ~ r1_tarski(k1_tops_1(A_112,k2_pre_topc(A_112,B_111)),B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_631,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_331,c_623])).

tff(c_648,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_36,c_153,c_421,c_631])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_648])).

tff(c_652,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_656,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_652,c_42])).

tff(c_651,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_695,plain,(
    ! [A_119,B_120] :
      ( k1_tops_1(A_119,k2_pre_topc(A_119,B_120)) = B_120
      | ~ v6_tops_1(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_699,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_695])).

tff(c_705,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_699])).

tff(c_747,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_tarski(k1_tops_1(A_131,B_132),k1_tops_1(A_131,C_133))
      | ~ r1_tarski(B_132,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_755,plain,(
    ! [B_132] :
      ( r1_tarski(k1_tops_1('#skF_1',B_132),'#skF_3')
      | ~ r1_tarski(B_132,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_747])).

tff(c_760,plain,(
    ! [B_132] :
      ( r1_tarski(k1_tops_1('#skF_1',B_132),'#skF_3')
      | ~ r1_tarski(B_132,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_755])).

tff(c_822,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_825,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_822])).

tff(c_829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_825])).

tff(c_831,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_867,plain,(
    ! [C_142,A_143] :
      ( ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_870,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_831,c_867])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_870])).

tff(c_885,plain,(
    ! [B_144,D_145] :
      ( k1_tops_1(B_144,D_145) = D_145
      | ~ v3_pre_topc(D_145,B_144)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(u1_struct_0(B_144)))
      | ~ l1_pre_topc(B_144) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_897,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_885])).

tff(c_908,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_651,c_897])).

tff(c_24,plain,(
    ! [A_16,B_20,C_22] :
      ( r1_tarski(k1_tops_1(A_16,B_20),k1_tops_1(A_16,C_22))
      | ~ r1_tarski(B_20,C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_933,plain,(
    ! [C_22] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_22))
      | ~ r1_tarski('#skF_4',C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_24])).

tff(c_968,plain,(
    ! [C_147] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_147))
      | ~ r1_tarski('#skF_4',C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_933])).

tff(c_972,plain,(
    ! [B_10] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_10)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_968])).

tff(c_978,plain,(
    ! [B_10] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_10)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_972])).

tff(c_719,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k1_tops_1(A_123,k2_pre_topc(A_123,B_124)),B_124)
      | ~ v4_tops_1(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1194,plain,(
    ! [A_164,B_165] :
      ( k1_tops_1(A_164,k2_pre_topc(A_164,B_165)) = B_165
      | ~ r1_tarski(B_165,k1_tops_1(A_164,k2_pre_topc(A_164,B_165)))
      | ~ v4_tops_1(B_165,A_164)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_719,c_2])).

tff(c_1198,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_978,c_1194])).

tff(c_1212,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_667,c_34,c_656,c_1198])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v6_tops_1(B_8,A_6)
      | k1_tops_1(A_6,k2_pre_topc(A_6,B_8)) != B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1251,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_14])).

tff(c_1276,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1251])).

tff(c_1278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1276])).

tff(c_1280,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1281,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1280,c_1281])).

tff(c_1283,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1279,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1427,plain,(
    ! [C_197,A_198] :
      ( ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1433,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1427])).

tff(c_1441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1433])).

tff(c_1443,plain,(
    ! [B_199,D_200] :
      ( k1_tops_1(B_199,D_200) = D_200
      | ~ v3_pre_topc(D_200,B_199)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(u1_struct_0(B_199)))
      | ~ l1_pre_topc(B_199) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1452,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1443])).

tff(c_1460,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1279,c_1452])).

tff(c_1464,plain,(
    ! [C_22] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_22))
      | ~ r1_tarski('#skF_4',C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_24])).

tff(c_1480,plain,(
    ! [C_201] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_201))
      | ~ r1_tarski('#skF_4',C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1464])).

tff(c_1484,plain,(
    ! [B_10] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_10)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_1480])).

tff(c_1490,plain,(
    ! [B_10] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_10)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1484])).

tff(c_1347,plain,(
    ! [A_178,B_179] :
      ( r1_tarski(k1_tops_1(A_178,k2_pre_topc(A_178,B_179)),B_179)
      | ~ v4_tops_1(B_179,A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1523,plain,(
    ! [A_209,B_210] :
      ( k1_tops_1(A_209,k2_pre_topc(A_209,B_210)) = B_210
      | ~ r1_tarski(B_210,k1_tops_1(A_209,k2_pre_topc(A_209,B_210)))
      | ~ v4_tops_1(B_210,A_209)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_1347,c_2])).

tff(c_1527,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1490,c_1523])).

tff(c_1534,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1304,c_34,c_1283,c_1527])).

tff(c_1585,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1534,c_14])).

tff(c_1610,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1585])).

tff(c_1612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1610])).

tff(c_1613,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1665,plain,(
    ! [A_221,B_222] :
      ( k1_tops_1(A_221,k2_pre_topc(A_221,B_222)) = B_222
      | ~ v6_tops_1(B_222,A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1669,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1665])).

tff(c_1675,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1613,c_1669])).

tff(c_1657,plain,(
    ! [A_219,B_220] :
      ( m1_subset_1(k2_pre_topc(A_219,B_220),k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1698,plain,(
    ! [A_225,B_226] :
      ( v3_pre_topc(k1_tops_1(A_225,k2_pre_topc(A_225,B_226)),A_225)
      | ~ v2_pre_topc(A_225)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225) ) ),
    inference(resolution,[status(thm)],[c_1657,c_20])).

tff(c_1704,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1675,c_1698])).

tff(c_1708,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_1704])).

tff(c_1710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1624,c_1708])).

tff(c_1712,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1711,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1713,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1711])).

tff(c_1718,plain,(
    ! [B_227,A_228] :
      ( r1_tarski(B_227,k2_pre_topc(A_228,B_227))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1720,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1718])).

tff(c_1725,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1720])).

tff(c_1970,plain,(
    ! [C_254,A_255] :
      ( ~ m1_subset_1(C_254,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1979,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1970])).

tff(c_1990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1979])).

tff(c_1992,plain,(
    ! [B_256,D_257] :
      ( k1_tops_1(B_256,D_257) = D_257
      | ~ v3_pre_topc(D_257,B_256)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(u1_struct_0(B_256)))
      | ~ l1_pre_topc(B_256) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2001,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1992])).

tff(c_2011,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1712,c_2001])).

tff(c_1756,plain,(
    ! [A_233,B_234] :
      ( k1_tops_1(A_233,k2_pre_topc(A_233,B_234)) = B_234
      | ~ v6_tops_1(B_234,A_233)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1760,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1756])).

tff(c_1766,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1613,c_1760])).

tff(c_2052,plain,(
    ! [B_259,A_260] :
      ( v4_tops_1(B_259,A_260)
      | ~ r1_tarski(B_259,k2_pre_topc(A_260,k1_tops_1(A_260,B_259)))
      | ~ r1_tarski(k1_tops_1(A_260,k2_pre_topc(A_260,B_259)),B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2065,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_2052])).

tff(c_2071,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_1725,c_2011,c_2065])).

tff(c_2073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1713,c_2071])).

tff(c_2075,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1711])).

tff(c_1614,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1712,c_2075,c_1614,c_40])).

%------------------------------------------------------------------------------
