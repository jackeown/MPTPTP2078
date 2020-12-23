%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:02 EST 2020

% Result     : Theorem 19.38s
% Output     : CNFRefutation 20.06s
% Verified   : 
% Statistics : Number of formulae       :  588 (16256 expanded)
%              Number of leaves         :   33 (5107 expanded)
%              Depth                    :   25
%              Number of atoms          : 1364 (50424 expanded)
%              Number of equality atoms :  280 (6956 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_compts_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ( v2_compts_1(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( B = k1_xboole_0
             => ( v2_compts_1(B,A)
              <=> v1_compts_1(k1_pre_topc(A,B)) ) )
            & ( v2_pre_topc(A)
             => ( B = k1_xboole_0
                | ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))
             => ( B = C
               => g1_pre_topc(u1_struct_0(k1_pre_topc(A,B)),u1_pre_topc(k1_pre_topc(A,B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_62,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_77,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_222,plain,(
    ! [A_75,B_76] :
      ( v1_compts_1(k1_pre_topc(A_75,B_76))
      | ~ v2_compts_1(B_76,A_75)
      | k1_xboole_0 = B_76
      | ~ v2_pre_topc(A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_228,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_222])).

tff(c_231,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_77,c_228])).

tff(c_232,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_38,plain,(
    ! [A_34] :
      ( v1_compts_1(k1_pre_topc(A_34,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_34)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_241,plain,(
    ! [A_77] :
      ( v1_compts_1(k1_pre_topc(A_77,'#skF_3'))
      | ~ v2_compts_1('#skF_3',A_77)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_232,c_232,c_38])).

tff(c_247,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_241])).

tff(c_250,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_77,c_247])).

tff(c_16,plain,(
    ! [A_13] :
      ( m1_subset_1(u1_pre_topc(A_13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,(
    ! [A_41,B_42] :
      ( l1_pre_topc(g1_pre_topc(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    ! [A_13] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_13),u1_pre_topc(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_105,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0(k1_pre_topc(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_108,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_105])).

tff(c_111,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_108])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( v1_pre_topc(g1_pre_topc(A_39,B_40))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [A_13] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_13),u1_pre_topc(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [C_59,A_60,D_61,B_62] :
      ( C_59 = A_60
      | g1_pre_topc(C_59,D_61) != g1_pre_topc(A_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_172,plain,(
    ! [A_1,A_60,B_62] :
      ( u1_struct_0(A_1) = A_60
      | g1_pre_topc(A_60,B_62) != A_1
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_60)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_321,plain,(
    ! [A_93,B_94] :
      ( u1_struct_0(g1_pre_topc(A_93,B_94)) = A_93
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k1_zfmisc_1(A_93)))
      | ~ v1_pre_topc(g1_pre_topc(A_93,B_94))
      | ~ l1_pre_topc(g1_pre_topc(A_93,B_94)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_172])).

tff(c_467,plain,(
    ! [A_104] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_104),u1_pre_topc(A_104))) = u1_struct_0(A_104)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_104),u1_pre_topc(A_104)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_104),u1_pre_topc(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_16,c_321])).

tff(c_482,plain,(
    ! [A_105] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105))) = u1_struct_0(A_105)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_68,c_467])).

tff(c_497,plain,(
    ! [A_106] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106))) = u1_struct_0(A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_73,c_482])).

tff(c_30,plain,(
    ! [A_27,C_33] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_27,C_33)),u1_pre_topc(k1_pre_topc(A_27,C_33))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_27),u1_pre_topc(A_27)),C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_27),u1_pre_topc(A_27)))))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2465,plain,(
    ! [A_157,C_158] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_157,C_158)),u1_pre_topc(k1_pre_topc(A_157,C_158))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_157),u1_pre_topc(A_157)),C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_30])).

tff(c_2621,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_2465])).

tff(c_2628,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_98,c_98,c_2621])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_pre_topc(k1_pre_topc(A_11,B_12))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_557,plain,(
    ! [A_106,B_12] :
      ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)),B_12))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_14])).

tff(c_2668,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_557])).

tff(c_2698,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_2668])).

tff(c_2746,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2698])).

tff(c_2752,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_2746])).

tff(c_2758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2752])).

tff(c_2760,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2698])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_pre_topc(k1_pre_topc(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1699,plain,(
    ! [A_135,B_136] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)),B_136),g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_12])).

tff(c_1761,plain,(
    ! [A_1,B_136] :
      ( m1_pre_topc(k1_pre_topc(A_1,B_136),g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1699])).

tff(c_2650,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_1761])).

tff(c_3138,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_2760,c_2650])).

tff(c_3139,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3138])).

tff(c_3145,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_3139])).

tff(c_3151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3145])).

tff(c_3153,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3138])).

tff(c_174,plain,(
    ! [A_1,C_59,D_61] :
      ( u1_struct_0(A_1) = C_59
      | g1_pre_topc(C_59,D_61) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_949,plain,(
    ! [C_121,D_122] :
      ( u1_struct_0(g1_pre_topc(C_121,D_122)) = C_121
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_121,D_122)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_121,D_122)))))
      | ~ v1_pre_topc(g1_pre_topc(C_121,D_122))
      | ~ l1_pre_topc(g1_pre_topc(C_121,D_122)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_174])).

tff(c_971,plain,(
    ! [C_121,D_122] :
      ( u1_struct_0(g1_pre_topc(C_121,D_122)) = C_121
      | ~ v1_pre_topc(g1_pre_topc(C_121,D_122))
      | ~ l1_pre_topc(g1_pre_topc(C_121,D_122)) ) ),
    inference(resolution,[status(thm)],[c_16,c_949])).

tff(c_3156,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3153,c_971])).

tff(c_3165,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_3156])).

tff(c_101,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_14])).

tff(c_104,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101])).

tff(c_141,plain,(
    ! [A_51,B_52] :
      ( m1_pre_topc(k1_pre_topc(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_145,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_141])).

tff(c_148,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_145])).

tff(c_290,plain,(
    ! [A_87,B_88] :
      ( k2_struct_0(k1_pre_topc(A_87,B_88)) = B_88
      | ~ m1_pre_topc(k1_pre_topc(A_87,B_88),A_87)
      | ~ v1_pre_topc(k1_pre_topc(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_292,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_148,c_290])).

tff(c_295,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_104,c_292])).

tff(c_4,plain,(
    ! [A_2,C_8] :
      ( k1_pre_topc(A_2,k2_struct_0(C_8)) = C_8
      | ~ m1_pre_topc(C_8,A_2)
      | ~ v1_pre_topc(C_8)
      | ~ m1_subset_1(k2_struct_0(C_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_299,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_4])).

tff(c_303,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_295,c_299])).

tff(c_3347,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3165,c_303])).

tff(c_3518,plain,
    ( g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_98,c_2628,c_3347])).

tff(c_4319,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3518])).

tff(c_28,plain,(
    ! [B_26,A_24] :
      ( m1_pre_topc(B_26,A_24)
      | ~ m1_pre_topc(B_26,g1_pre_topc(u1_struct_0(A_24),u1_pre_topc(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1766,plain,(
    ! [A_135,B_136] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)),B_136),A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_1699,c_28])).

tff(c_2653,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),'#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_1766])).

tff(c_2688,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),'#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_2653])).

tff(c_2777,plain,(
    m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_2688])).

tff(c_2759,plain,(
    v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_2698])).

tff(c_551,plain,(
    ! [A_106,B_12] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)),B_12),g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_12])).

tff(c_2656,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_551])).

tff(c_2690,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_2656])).

tff(c_3125,plain,(
    m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_2690])).

tff(c_6,plain,(
    ! [A_2,B_6] :
      ( k2_struct_0(k1_pre_topc(A_2,B_6)) = B_6
      | ~ m1_pre_topc(k1_pre_topc(A_2,B_6),A_2)
      | ~ v1_pre_topc(k1_pre_topc(A_2,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2670,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3')) = '#skF_3'
    | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_6])).

tff(c_2699,plain,
    ( k2_struct_0(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))) = '#skF_3'
    | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2628,c_2628,c_2670])).

tff(c_4309,plain,(
    k2_struct_0(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_98,c_3165,c_2759,c_3125,c_2699])).

tff(c_4313,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))) = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),A_2)
      | ~ v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4309,c_4])).

tff(c_6110,plain,(
    ! [A_223] :
      ( k1_pre_topc(A_223,'#skF_3') = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),A_223)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2759,c_4309,c_4313])).

tff(c_6116,plain,
    ( g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2777,c_6110])).

tff(c_6122,plain,(
    g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_6116])).

tff(c_6198,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6122,c_3125])).

tff(c_6207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4319,c_6198])).

tff(c_6208,plain,(
    g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3518])).

tff(c_50,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_188,plain,(
    ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_36,plain,(
    ! [A_34] :
      ( v2_compts_1(k1_xboole_0,A_34)
      | ~ v1_compts_1(k1_pre_topc(A_34,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_236,plain,(
    ! [A_34] :
      ( v2_compts_1('#skF_3',A_34)
      | ~ v1_compts_1(k1_pre_topc(A_34,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_232,c_232,c_36])).

tff(c_540,plain,(
    ! [A_106] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_236])).

tff(c_2641,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_compts_1(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_540])).

tff(c_2681,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_compts_1(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_2641])).

tff(c_2682,plain,
    ( ~ v1_compts_1(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_2681])).

tff(c_2767,plain,(
    ~ v1_compts_1(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_2682])).

tff(c_6216,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6208,c_2767])).

tff(c_6224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_6216])).

tff(c_6226,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_6225,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_6243,plain,(
    ! [A_233,B_234] :
      ( u1_struct_0(g1_pre_topc(A_233,B_234)) = A_233
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k1_zfmisc_1(A_233)))
      | ~ v1_pre_topc(g1_pre_topc(A_233,B_234))
      | ~ l1_pre_topc(g1_pre_topc(A_233,B_234)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_172])).

tff(c_6279,plain,(
    ! [A_240] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240))) = u1_struct_0(A_240)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(resolution,[status(thm)],[c_16,c_6243])).

tff(c_6291,plain,(
    ! [A_241] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_241),u1_pre_topc(A_241))) = u1_struct_0(A_241)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_241),u1_pre_topc(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_68,c_6279])).

tff(c_6302,plain,(
    ! [A_13] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_13),u1_pre_topc(A_13))) = u1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_73,c_6291])).

tff(c_6406,plain,(
    ! [A_245,C_246] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_245,C_246)),u1_pre_topc(k1_pre_topc(A_245,C_246))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_245),u1_pre_topc(A_245)),C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_245),u1_pre_topc(A_245)))))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8460,plain,(
    ! [A_303,C_304] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_303,C_304)),u1_pre_topc(k1_pre_topc(A_303,C_304))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_303),u1_pre_topc(A_303)),C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(u1_struct_0(A_303)))
      | ~ m1_subset_1(C_304,k1_zfmisc_1(u1_struct_0(A_303)))
      | ~ l1_pre_topc(A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6302,c_6406])).

tff(c_8621,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_8460])).

tff(c_8629,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_98,c_98,c_8621])).

tff(c_6303,plain,(
    ! [A_242] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242))) = u1_struct_0(A_242)
      | ~ l1_pre_topc(A_242) ) ),
    inference(resolution,[status(thm)],[c_73,c_6291])).

tff(c_6338,plain,(
    ! [A_242,B_12] :
      ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)),B_12))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6303,c_14])).

tff(c_8666,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8629,c_6338])).

tff(c_8696,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_8666])).

tff(c_8703,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8696])).

tff(c_8755,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_8703])).

tff(c_8761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8755])).

tff(c_8763,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8696])).

tff(c_7824,plain,(
    ! [A_285,B_286] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_285),u1_pre_topc(A_285)),B_286),g1_pre_topc(u1_struct_0(A_285),u1_pre_topc(A_285)))
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_285),u1_pre_topc(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6303,c_12])).

tff(c_7889,plain,(
    ! [A_1,B_286] :
      ( m1_pre_topc(k1_pre_topc(A_1,B_286),g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)))
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7824])).

tff(c_8642,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8629,c_7889])).

tff(c_8778,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_8763,c_8642])).

tff(c_8779,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8778])).

tff(c_8785,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_8779])).

tff(c_8791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8785])).

tff(c_8793,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8778])).

tff(c_6874,plain,(
    ! [C_262,D_263] :
      ( u1_struct_0(g1_pre_topc(C_262,D_263)) = C_262
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_262,D_263)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_262,D_263)))))
      | ~ v1_pre_topc(g1_pre_topc(C_262,D_263))
      | ~ l1_pre_topc(g1_pre_topc(C_262,D_263)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_174])).

tff(c_6896,plain,(
    ! [C_262,D_263] :
      ( u1_struct_0(g1_pre_topc(C_262,D_263)) = C_262
      | ~ v1_pre_topc(g1_pre_topc(C_262,D_263))
      | ~ l1_pre_topc(g1_pre_topc(C_262,D_263)) ) ),
    inference(resolution,[status(thm)],[c_16,c_6874])).

tff(c_8799,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8793,c_6896])).

tff(c_8808,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_8799])).

tff(c_128,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_73])).

tff(c_140,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_6253,plain,(
    ! [A_237,B_238] :
      ( k2_struct_0(k1_pre_topc(A_237,B_238)) = B_238
      | ~ m1_pre_topc(k1_pre_topc(A_237,B_238),A_237)
      | ~ v1_pre_topc(k1_pre_topc(A_237,B_238))
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6255,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_148,c_6253])).

tff(c_6258,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_104,c_6255])).

tff(c_6262,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6258,c_4])).

tff(c_6266,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_6258,c_6262])).

tff(c_6476,plain,(
    ! [A_251] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6303,c_6266])).

tff(c_6730,plain,(
    ! [A_259] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_259),u1_pre_topc(A_259)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_259)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_259),u1_pre_topc(A_259)))
      | ~ l1_pre_topc(A_259)
      | ~ v1_pre_topc(A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6476])).

tff(c_7711,plain,(
    ! [A_282] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_282)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ v1_pre_topc(A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(resolution,[status(thm)],[c_73,c_6730])).

tff(c_6614,plain,(
    ! [A_256,C_257] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_256,C_257)),u1_pre_topc(k1_pre_topc(A_256,C_257))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_256),u1_pre_topc(A_256)),C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256)
      | ~ v1_pre_topc(A_256)
      | ~ l1_pre_topc(A_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6406])).

tff(c_6674,plain,(
    ! [A_256,C_257] :
      ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_256),u1_pre_topc(A_256)),C_257))
      | ~ l1_pre_topc(k1_pre_topc(A_256,C_257))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256)
      | ~ v1_pre_topc(A_256)
      | ~ l1_pre_topc(A_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6614,c_73])).

tff(c_7723,plain,(
    ! [A_282] :
      ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc(k1_pre_topc(A_282,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ v1_pre_topc(A_282)
      | ~ l1_pre_topc(A_282)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_282)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ v1_pre_topc(A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7711,c_6674])).

tff(c_7773,plain,(
    ! [A_282] :
      ( ~ l1_pre_topc(k1_pre_topc(A_282,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ v1_pre_topc(A_282)
      | ~ l1_pre_topc(A_282)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_282)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ v1_pre_topc(A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_7723])).

tff(c_9178,plain,
    ( ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8808,c_7773])).

tff(c_9381,plain,
    ( ~ l1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_8793,c_98,c_8808,c_8763,c_8793,c_8763,c_98,c_8808,c_98,c_8629,c_9178])).

tff(c_10126,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9381])).

tff(c_7894,plain,(
    ! [A_285,B_286] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_285),u1_pre_topc(A_285)),B_286),A_285)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_285),u1_pre_topc(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(resolution,[status(thm)],[c_7824,c_28])).

tff(c_8645,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),'#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8629,c_7894])).

tff(c_8682,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),'#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_8645])).

tff(c_9880,plain,(
    m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_8682])).

tff(c_8762,plain,(
    v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_8696])).

tff(c_6332,plain,(
    ! [A_242,B_12] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)),B_12),g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6303,c_12])).

tff(c_8648,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8629,c_6332])).

tff(c_8684,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_8648])).

tff(c_10112,plain,(
    m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_8684])).

tff(c_8668,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3')) = '#skF_3'
    | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8629,c_6])).

tff(c_8697,plain,
    ( k2_struct_0(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))) = '#skF_3'
    | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8629,c_8629,c_8668])).

tff(c_10325,plain,(
    k2_struct_0(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_98,c_8808,c_8762,c_10112,c_8697])).

tff(c_10329,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))) = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),A_2)
      | ~ v1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10325,c_4])).

tff(c_12390,plain,(
    ! [A_375] :
      ( k1_pre_topc(A_375,'#skF_3') = g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))),A_375)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_pre_topc(A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8762,c_10325,c_10329])).

tff(c_12396,plain,
    ( g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_9880,c_12390])).

tff(c_12402,plain,(
    g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_12396])).

tff(c_12489,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12402,c_10112])).

tff(c_12496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10126,c_12489])).

tff(c_12498,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_9381])).

tff(c_6312,plain,(
    ! [A_242] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6303,c_6266])).

tff(c_12501,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12498,c_6312])).

tff(c_12510,plain,(
    g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8763,c_98,c_8629,c_12501])).

tff(c_12521,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12510,c_8629])).

tff(c_18,plain,(
    ! [A_14] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_14),u1_pre_topc(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_34,B_36] :
      ( v1_compts_1(k1_pre_topc(A_34,B_36))
      | ~ v2_compts_1(B_36,A_34)
      | k1_xboole_0 = B_36
      | ~ v2_pre_topc(A_34)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_9302,plain,(
    ! [B_36] :
      ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_36))
      | ~ v2_compts_1(B_36,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | k1_xboole_0 = B_36
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8808,c_34])).

tff(c_9466,plain,(
    ! [B_36] :
      ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_36))
      | ~ v2_compts_1(B_36,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | k1_xboole_0 = B_36
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_9302])).

tff(c_23361,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9466])).

tff(c_23367,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_23361])).

tff(c_23373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_23367])).

tff(c_23375,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_9466])).

tff(c_32,plain,(
    ! [B_36,A_34] :
      ( v2_compts_1(B_36,A_34)
      | ~ v1_compts_1(k1_pre_topc(A_34,B_36))
      | k1_xboole_0 = B_36
      | ~ v2_pre_topc(A_34)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_9305,plain,(
    ! [B_36] :
      ( v2_compts_1(B_36,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_36))
      | k1_xboole_0 = B_36
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8808,c_32])).

tff(c_9468,plain,(
    ! [B_36] :
      ( v2_compts_1(B_36,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_36))
      | k1_xboole_0 = B_36
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8763,c_9305])).

tff(c_23426,plain,(
    ! [B_577] :
      ( v2_compts_1(B_577,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_577))
      | k1_xboole_0 = B_577
      | ~ m1_subset_1(B_577,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23375,c_9468])).

tff(c_23441,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12521,c_23426])).

tff(c_23459,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_6225,c_23441])).

tff(c_23461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6226,c_188,c_23459])).

tff(c_23463,plain,(
    v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_23608,plain,(
    ! [A_606,B_607] :
      ( u1_struct_0(g1_pre_topc(A_606,B_607)) = A_606
      | ~ m1_subset_1(B_607,k1_zfmisc_1(k1_zfmisc_1(A_606)))
      | ~ v1_pre_topc(g1_pre_topc(A_606,B_607))
      | ~ l1_pre_topc(g1_pre_topc(A_606,B_607)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_172])).

tff(c_23810,plain,(
    ! [A_617] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_617),u1_pre_topc(A_617))) = u1_struct_0(A_617)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_617),u1_pre_topc(A_617)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_617),u1_pre_topc(A_617)))
      | ~ l1_pre_topc(A_617) ) ),
    inference(resolution,[status(thm)],[c_16,c_23608])).

tff(c_23828,plain,(
    ! [A_618] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_618),u1_pre_topc(A_618))) = u1_struct_0(A_618)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_618),u1_pre_topc(A_618)))
      | ~ l1_pre_topc(A_618) ) ),
    inference(resolution,[status(thm)],[c_68,c_23810])).

tff(c_23846,plain,(
    ! [A_619] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_619),u1_pre_topc(A_619))) = u1_struct_0(A_619)
      | ~ l1_pre_topc(A_619) ) ),
    inference(resolution,[status(thm)],[c_73,c_23828])).

tff(c_23462,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_23469,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_23462])).

tff(c_23895,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23846,c_23469])).

tff(c_23946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98,c_23895])).

tff(c_23948,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_23462])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_23992,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23463,c_23948,c_46])).

tff(c_23993,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_23992])).

tff(c_48,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_27327,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23463,c_23948,c_48])).

tff(c_27625,plain,(
    ! [A_719,C_720] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_719,C_720)),u1_pre_topc(k1_pre_topc(A_719,C_720))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_719),u1_pre_topc(A_719)),C_720)
      | ~ m1_subset_1(C_720,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_719),u1_pre_topc(A_719)))))
      | ~ m1_subset_1(C_720,k1_zfmisc_1(u1_struct_0(A_719)))
      | ~ l1_pre_topc(A_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_27629,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27327,c_27625])).

tff(c_27641,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27629])).

tff(c_27666,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_27641])).

tff(c_23968,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_23948,c_14])).

tff(c_23971,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_23968])).

tff(c_23977,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_23971])).

tff(c_23983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_23977])).

tff(c_23985,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_23968])).

tff(c_27597,plain,(
    ! [A_716,B_717] :
      ( u1_struct_0(g1_pre_topc(A_716,B_717)) = A_716
      | ~ m1_subset_1(B_717,k1_zfmisc_1(k1_zfmisc_1(A_716)))
      | ~ v1_pre_topc(g1_pre_topc(A_716,B_717))
      | ~ l1_pre_topc(g1_pre_topc(A_716,B_717)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_172])).

tff(c_27817,plain,(
    ! [A_723] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_723),u1_pre_topc(A_723))) = u1_struct_0(A_723)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_723),u1_pre_topc(A_723)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_723),u1_pre_topc(A_723)))
      | ~ l1_pre_topc(A_723) ) ),
    inference(resolution,[status(thm)],[c_16,c_27597])).

tff(c_27841,plain,(
    ! [A_724] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_724),u1_pre_topc(A_724))) = u1_struct_0(A_724)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_724),u1_pre_topc(A_724)))
      | ~ l1_pre_topc(A_724) ) ),
    inference(resolution,[status(thm)],[c_68,c_27817])).

tff(c_27853,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_23985,c_27841])).

tff(c_27867,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27853])).

tff(c_27870,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27867,c_27327])).

tff(c_27873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27666,c_27870])).

tff(c_27875,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_27641])).

tff(c_27881,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27875,c_32])).

tff(c_27895,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_27881])).

tff(c_27896,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_23993,c_27895])).

tff(c_27964,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_27896])).

tff(c_26,plain,(
    ! [A_21,B_23] :
      ( u1_struct_0(k1_pre_topc(A_21,B_23)) = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_27886,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27875,c_26])).

tff(c_27902,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27886])).

tff(c_27874,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_27641])).

tff(c_28048,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27902,c_27874])).

tff(c_27889,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27875,c_14])).

tff(c_27905,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27889])).

tff(c_27883,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27875,c_12])).

tff(c_27899,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27883])).

tff(c_27907,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27899,c_6])).

tff(c_27910,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27875,c_27905,c_27907])).

tff(c_27968,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27910,c_4])).

tff(c_31566,plain,(
    ! [A_810] :
      ( k1_pre_topc(A_810,'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_810)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_810)))
      | ~ l1_pre_topc(A_810) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27905,c_27910,c_27968])).

tff(c_31578,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_27327,c_31566])).

tff(c_31588,plain,
    ( g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23985,c_28048,c_31578])).

tff(c_31611,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_31588])).

tff(c_27335,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_27327,c_12])).

tff(c_27353,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23985,c_27335])).

tff(c_27421,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27353,c_28])).

tff(c_27430,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27421])).

tff(c_28052,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28048,c_27430])).

tff(c_27341,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_27327,c_14])).

tff(c_27359,plain,(
    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23985,c_27341])).

tff(c_28055,plain,(
    v1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28048,c_27359])).

tff(c_27525,plain,(
    ! [A_709,B_710] :
      ( k2_struct_0(k1_pre_topc(A_709,B_710)) = B_710
      | ~ m1_pre_topc(k1_pre_topc(A_709,B_710),A_709)
      | ~ v1_pre_topc(k1_pre_topc(A_709,B_710))
      | ~ m1_subset_1(B_710,k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ l1_pre_topc(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_27529,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_27353,c_27525])).

tff(c_27537,plain,(
    k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23985,c_27327,c_27359,c_27529])).

tff(c_28050,plain,(
    k2_struct_0(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28048,c_27537])).

tff(c_28072,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))))) = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),A_2)
      | ~ v1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28050,c_4])).

tff(c_35412,plain,(
    ! [A_879] :
      ( k1_pre_topc(A_879,'#skF_2') = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),A_879)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_879)))
      | ~ l1_pre_topc(A_879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28055,c_28050,c_28072])).

tff(c_35418,plain,
    ( g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28052,c_35412])).

tff(c_35424,plain,(
    g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_27875,c_35418])).

tff(c_28053,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28048,c_27353])).

tff(c_35426,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35424,c_28053])).

tff(c_35435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31611,c_35426])).

tff(c_35436,plain,(
    g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_31588])).

tff(c_23947,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_23462])).

tff(c_27330,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_27327,c_34])).

tff(c_27347,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23985,c_23947,c_27330])).

tff(c_27440,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_27347])).

tff(c_27466,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_27440])).

tff(c_27472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_27466])).

tff(c_27473,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_27347])).

tff(c_27503,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_27473])).

tff(c_28051,plain,(
    v1_compts_1(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28048,c_27503])).

tff(c_35442,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35436,c_28051])).

tff(c_35450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27964,c_35442])).

tff(c_35452,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_27896])).

tff(c_35451,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_27896])).

tff(c_35616,plain,(
    ! [A_880] :
      ( v2_compts_1('#skF_2',A_880)
      | ~ v1_compts_1(k1_pre_topc(A_880,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_880)))
      | ~ l1_pre_topc(A_880) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35451,c_35451,c_35451,c_36])).

tff(c_35628,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27875,c_35616])).

tff(c_35637,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_35452,c_35628])).

tff(c_35639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23993,c_35637])).

tff(c_35641,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_27473])).

tff(c_35640,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_27473])).

tff(c_35717,plain,(
    ! [A_883] :
      ( v1_compts_1(k1_pre_topc(A_883,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_883)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_883)))
      | ~ l1_pre_topc(A_883) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35640,c_35640,c_35640,c_38])).

tff(c_35723,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_27327,c_35717])).

tff(c_35732,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23985,c_23947,c_35723])).

tff(c_35734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35641,c_35732])).

tff(c_35735,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_23992])).

tff(c_36181,plain,(
    ! [A_908,B_909] :
      ( u1_struct_0(g1_pre_topc(A_908,B_909)) = A_908
      | ~ m1_subset_1(B_909,k1_zfmisc_1(k1_zfmisc_1(A_908)))
      | ~ v1_pre_topc(g1_pre_topc(A_908,B_909))
      | ~ l1_pre_topc(g1_pre_topc(A_908,B_909)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_172])).

tff(c_36405,plain,(
    ! [A_915] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_915),u1_pre_topc(A_915))) = u1_struct_0(A_915)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_915),u1_pre_topc(A_915)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_915),u1_pre_topc(A_915)))
      | ~ l1_pre_topc(A_915) ) ),
    inference(resolution,[status(thm)],[c_16,c_36181])).

tff(c_36429,plain,(
    ! [A_916] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_916),u1_pre_topc(A_916))) = u1_struct_0(A_916)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_916),u1_pre_topc(A_916)))
      | ~ l1_pre_topc(A_916) ) ),
    inference(resolution,[status(thm)],[c_68,c_36405])).

tff(c_36441,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_23985,c_36429])).

tff(c_36455,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36441])).

tff(c_35799,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23463,c_23948,c_48])).

tff(c_36459,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36455,c_35799])).

tff(c_36462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35735,c_36459])).

tff(c_36464,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_36478,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36464,c_52])).

tff(c_36479,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36478])).

tff(c_54,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_36498,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_36464,c_54])).

tff(c_36747,plain,(
    ! [A_958,C_959] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_958,C_959)),u1_pre_topc(k1_pre_topc(A_958,C_959))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_958),u1_pre_topc(A_958)),C_959)
      | ~ m1_subset_1(C_959,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_958),u1_pre_topc(A_958)))))
      | ~ m1_subset_1(C_959,k1_zfmisc_1(u1_struct_0(A_958)))
      | ~ l1_pre_topc(A_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36751,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36498,c_36747])).

tff(c_36757,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36751])).

tff(c_36883,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_36757])).

tff(c_36512,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36498,c_14])).

tff(c_36517,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_36512])).

tff(c_36523,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_36517])).

tff(c_36529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36523])).

tff(c_36531,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_36512])).

tff(c_36484,plain,(
    ! [D_923,B_924,C_925,A_926] :
      ( D_923 = B_924
      | g1_pre_topc(C_925,D_923) != g1_pre_topc(A_926,B_924)
      | ~ m1_subset_1(B_924,k1_zfmisc_1(k1_zfmisc_1(A_926))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36486,plain,(
    ! [A_1,B_924,A_926] :
      ( u1_pre_topc(A_1) = B_924
      | g1_pre_topc(A_926,B_924) != A_1
      | ~ m1_subset_1(B_924,k1_zfmisc_1(k1_zfmisc_1(A_926)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36484])).

tff(c_36680,plain,(
    ! [A_955,B_956] :
      ( u1_pre_topc(g1_pre_topc(A_955,B_956)) = B_956
      | ~ m1_subset_1(B_956,k1_zfmisc_1(k1_zfmisc_1(A_955)))
      | ~ v1_pre_topc(g1_pre_topc(A_955,B_956))
      | ~ l1_pre_topc(g1_pre_topc(A_955,B_956)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_36486])).

tff(c_36735,plain,(
    ! [A_957] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_957),u1_pre_topc(A_957))) = u1_pre_topc(A_957)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_957),u1_pre_topc(A_957)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_957),u1_pre_topc(A_957)))
      | ~ l1_pre_topc(A_957) ) ),
    inference(resolution,[status(thm)],[c_16,c_36680])).

tff(c_36758,plain,(
    ! [A_960] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_960),u1_pre_topc(A_960))) = u1_pre_topc(A_960)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_960),u1_pre_topc(A_960)))
      | ~ l1_pre_topc(A_960) ) ),
    inference(resolution,[status(thm)],[c_68,c_36735])).

tff(c_36764,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36531,c_36758])).

tff(c_36774,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36764])).

tff(c_36799,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36774,c_16])).

tff(c_36820,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36799])).

tff(c_36493,plain,(
    ! [C_927,A_928,D_929,B_930] :
      ( C_927 = A_928
      | g1_pre_topc(C_927,D_929) != g1_pre_topc(A_928,B_930)
      | ~ m1_subset_1(B_930,k1_zfmisc_1(k1_zfmisc_1(A_928))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36497,plain,(
    ! [A_1,C_927,D_929] :
      ( u1_struct_0(A_1) = C_927
      | g1_pre_topc(C_927,D_929) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_36493])).

tff(c_37370,plain,(
    ! [C_971,D_972] :
      ( u1_struct_0(g1_pre_topc(C_971,D_972)) = C_971
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_971,D_972)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_971,D_972)))))
      | ~ v1_pre_topc(g1_pre_topc(C_971,D_972))
      | ~ l1_pre_topc(g1_pre_topc(C_971,D_972)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_36497])).

tff(c_37388,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36774,c_37370])).

tff(c_37403,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36820,c_37388])).

tff(c_37426,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_37403])).

tff(c_37432,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_37426])).

tff(c_37438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37432])).

tff(c_37439,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_37403])).

tff(c_37466,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37439,c_36498])).

tff(c_37472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36883,c_37466])).

tff(c_37474,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_36757])).

tff(c_37480,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37474,c_32])).

tff(c_37494,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_37480])).

tff(c_37495,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36479,c_37494])).

tff(c_37593,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_37495])).

tff(c_37483,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37474,c_26])).

tff(c_37498,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37483])).

tff(c_37473,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_36757])).

tff(c_37558,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37498,c_37473])).

tff(c_38021,plain,(
    ! [C_981,D_982] :
      ( u1_struct_0(g1_pre_topc(C_981,D_982)) = C_981
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_981,D_982)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_981,D_982)))))
      | ~ v1_pre_topc(g1_pre_topc(C_981,D_982))
      | ~ l1_pre_topc(g1_pre_topc(C_981,D_982)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_36497])).

tff(c_38042,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36774,c_38021])).

tff(c_38059,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36820,c_38042])).

tff(c_38083,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_38059])).

tff(c_38089,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_38083])).

tff(c_38095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38089])).

tff(c_38096,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_38059])).

tff(c_37488,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37474,c_14])).

tff(c_37504,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37488])).

tff(c_37485,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37474,c_12])).

tff(c_37501,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37485])).

tff(c_37580,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37501,c_6])).

tff(c_37583,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37474,c_37504,c_37580])).

tff(c_37587,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37583,c_4])).

tff(c_38462,plain,(
    ! [A_989] :
      ( k1_pre_topc(A_989,'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_989)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_989)))
      | ~ l1_pre_topc(A_989) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37504,c_37583,c_37587])).

tff(c_38471,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38096,c_38462])).

tff(c_38482,plain,
    ( g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_37474,c_37558,c_38471])).

tff(c_38807,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_38482])).

tff(c_36511,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36498,c_12])).

tff(c_36686,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36511])).

tff(c_36691,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36686,c_28])).

tff(c_36703,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36691])).

tff(c_37560,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37558,c_36703])).

tff(c_36530,plain,(
    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36512])).

tff(c_37565,plain,(
    v1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37558,c_36530])).

tff(c_36688,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36686,c_6])).

tff(c_36700,plain,(
    k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36498,c_36530,c_36688])).

tff(c_37561,plain,(
    k2_struct_0(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37558,c_36700])).

tff(c_37597,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))))) = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),A_2)
      | ~ v1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37561,c_4])).

tff(c_40292,plain,(
    ! [A_1041] :
      ( k1_pre_topc(A_1041,'#skF_2') = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),A_1041)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(A_1041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37565,c_37561,c_37597])).

tff(c_40298,plain,
    ( g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37560,c_40292])).

tff(c_40304,plain,(
    g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37474,c_40298])).

tff(c_37562,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37558,c_36686])).

tff(c_40367,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40304,c_37562])).

tff(c_40376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38807,c_40367])).

tff(c_40377,plain,(
    g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38482])).

tff(c_36463,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_36620,plain,(
    ! [A_943,B_944] :
      ( v1_compts_1(k1_pre_topc(A_943,B_944))
      | ~ v2_compts_1(B_944,A_943)
      | k1_xboole_0 = B_944
      | ~ v2_pre_topc(A_943)
      | ~ m1_subset_1(B_944,k1_zfmisc_1(u1_struct_0(A_943)))
      | ~ l1_pre_topc(A_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36626,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36498,c_36620])).

tff(c_36629,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36463,c_36626])).

tff(c_36630,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_36629])).

tff(c_36636,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_36630])).

tff(c_36642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36636])).

tff(c_36643,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36629])).

tff(c_36651,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_36643])).

tff(c_37563,plain,(
    v1_compts_1(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37558,c_36651])).

tff(c_40384,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40377,c_37563])).

tff(c_40391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37593,c_40384])).

tff(c_40393,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_37495])).

tff(c_40392,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_37495])).

tff(c_40639,plain,(
    ! [A_1049] :
      ( v2_compts_1('#skF_2',A_1049)
      | ~ v1_compts_1(k1_pre_topc(A_1049,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1049)))
      | ~ l1_pre_topc(A_1049) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40392,c_40392,c_40392,c_36])).

tff(c_40648,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37474,c_40639])).

tff(c_40654,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40393,c_40648])).

tff(c_40656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36479,c_40654])).

tff(c_40658,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36643])).

tff(c_40657,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36643])).

tff(c_40672,plain,(
    ! [A_1050] :
      ( v1_compts_1(k1_pre_topc(A_1050,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_1050)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1050)))
      | ~ l1_pre_topc(A_1050) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40657,c_40657,c_40657,c_38])).

tff(c_40678,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36498,c_40672])).

tff(c_40681,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36463,c_40678])).

tff(c_40683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40658,c_40681])).

tff(c_40684,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_36478])).

tff(c_40704,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_36464,c_54])).

tff(c_40718,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_40704,c_14])).

tff(c_40725,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_40718])).

tff(c_40731,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_40725])).

tff(c_40737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40731])).

tff(c_40739,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40718])).

tff(c_40690,plain,(
    ! [D_1051,B_1052,C_1053,A_1054] :
      ( D_1051 = B_1052
      | g1_pre_topc(C_1053,D_1051) != g1_pre_topc(A_1054,B_1052)
      | ~ m1_subset_1(B_1052,k1_zfmisc_1(k1_zfmisc_1(A_1054))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40692,plain,(
    ! [A_1,B_1052,A_1054] :
      ( u1_pre_topc(A_1) = B_1052
      | g1_pre_topc(A_1054,B_1052) != A_1
      | ~ m1_subset_1(B_1052,k1_zfmisc_1(k1_zfmisc_1(A_1054)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40690])).

tff(c_40890,plain,(
    ! [A_1083,B_1084] :
      ( u1_pre_topc(g1_pre_topc(A_1083,B_1084)) = B_1084
      | ~ m1_subset_1(B_1084,k1_zfmisc_1(k1_zfmisc_1(A_1083)))
      | ~ v1_pre_topc(g1_pre_topc(A_1083,B_1084))
      | ~ l1_pre_topc(g1_pre_topc(A_1083,B_1084)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_40692])).

tff(c_40955,plain,(
    ! [A_1087] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1087),u1_pre_topc(A_1087))) = u1_pre_topc(A_1087)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1087),u1_pre_topc(A_1087)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1087),u1_pre_topc(A_1087)))
      | ~ l1_pre_topc(A_1087) ) ),
    inference(resolution,[status(thm)],[c_16,c_40890])).

tff(c_41020,plain,(
    ! [A_1090] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1090),u1_pre_topc(A_1090))) = u1_pre_topc(A_1090)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1090),u1_pre_topc(A_1090)))
      | ~ l1_pre_topc(A_1090) ) ),
    inference(resolution,[status(thm)],[c_68,c_40955])).

tff(c_41029,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40739,c_41020])).

tff(c_41039,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_41029])).

tff(c_41064,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41039,c_16])).

tff(c_41085,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40739,c_41064])).

tff(c_40699,plain,(
    ! [C_1055,A_1056,D_1057,B_1058] :
      ( C_1055 = A_1056
      | g1_pre_topc(C_1055,D_1057) != g1_pre_topc(A_1056,B_1058)
      | ~ m1_subset_1(B_1058,k1_zfmisc_1(k1_zfmisc_1(A_1056))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40703,plain,(
    ! [A_1,C_1055,D_1057] :
      ( u1_struct_0(A_1) = C_1055
      | g1_pre_topc(C_1055,D_1057) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40699])).

tff(c_41424,plain,(
    ! [C_1096,D_1097] :
      ( u1_struct_0(g1_pre_topc(C_1096,D_1097)) = C_1096
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_1096,D_1097)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1096,D_1097)))))
      | ~ v1_pre_topc(g1_pre_topc(C_1096,D_1097))
      | ~ l1_pre_topc(g1_pre_topc(C_1096,D_1097)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_40703])).

tff(c_41436,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41039,c_41424])).

tff(c_41457,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40739,c_41085,c_41436])).

tff(c_41476,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_41457])).

tff(c_41482,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_41476])).

tff(c_41488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_41482])).

tff(c_41489,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_41457])).

tff(c_41515,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41489,c_40704])).

tff(c_41521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40684,c_41515])).

tff(c_41523,plain,(
    ~ v2_compts_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_41548,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_41523,c_58])).

tff(c_41549,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_41548])).

tff(c_60,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_41558,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_41523,c_60])).

tff(c_42032,plain,(
    ! [A_1146,C_1147] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_1146,C_1147)),u1_pre_topc(k1_pre_topc(A_1146,C_1147))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_1146),u1_pre_topc(A_1146)),C_1147)
      | ~ m1_subset_1(C_1147,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1146),u1_pre_topc(A_1146)))))
      | ~ m1_subset_1(C_1147,k1_zfmisc_1(u1_struct_0(A_1146)))
      | ~ l1_pre_topc(A_1146) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42042,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_41558,c_42032])).

tff(c_42052,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42042])).

tff(c_42068,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_42052])).

tff(c_41572,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_41558,c_14])).

tff(c_41596,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_41572])).

tff(c_41602,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_41596])).

tff(c_41608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_41602])).

tff(c_41610,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_41572])).

tff(c_41579,plain,(
    ! [D_1109,B_1110,C_1111,A_1112] :
      ( D_1109 = B_1110
      | g1_pre_topc(C_1111,D_1109) != g1_pre_topc(A_1112,B_1110)
      | ~ m1_subset_1(B_1110,k1_zfmisc_1(k1_zfmisc_1(A_1112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41581,plain,(
    ! [A_1,B_1110,A_1112] :
      ( u1_pre_topc(A_1) = B_1110
      | g1_pre_topc(A_1112,B_1110) != A_1
      | ~ m1_subset_1(B_1110,k1_zfmisc_1(k1_zfmisc_1(A_1112)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_41579])).

tff(c_41754,plain,(
    ! [A_1137,B_1138] :
      ( u1_pre_topc(g1_pre_topc(A_1137,B_1138)) = B_1138
      | ~ m1_subset_1(B_1138,k1_zfmisc_1(k1_zfmisc_1(A_1137)))
      | ~ v1_pre_topc(g1_pre_topc(A_1137,B_1138))
      | ~ l1_pre_topc(g1_pre_topc(A_1137,B_1138)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_41581])).

tff(c_41813,plain,(
    ! [A_1143] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1143),u1_pre_topc(A_1143))) = u1_pre_topc(A_1143)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1143),u1_pre_topc(A_1143)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1143),u1_pre_topc(A_1143)))
      | ~ l1_pre_topc(A_1143) ) ),
    inference(resolution,[status(thm)],[c_16,c_41754])).

tff(c_41825,plain,(
    ! [A_1144] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1144),u1_pre_topc(A_1144))) = u1_pre_topc(A_1144)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1144),u1_pre_topc(A_1144)))
      | ~ l1_pre_topc(A_1144) ) ),
    inference(resolution,[status(thm)],[c_68,c_41813])).

tff(c_41831,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_41610,c_41825])).

tff(c_41841,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_41831])).

tff(c_41853,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41841,c_2])).

tff(c_41876,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_41853])).

tff(c_42503,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_41876])).

tff(c_42509,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_42503])).

tff(c_42515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42509])).

tff(c_42517,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_41876])).

tff(c_41865,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41841,c_16])).

tff(c_41884,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_41865])).

tff(c_41588,plain,(
    ! [C_1113,A_1114,D_1115,B_1116] :
      ( C_1113 = A_1114
      | g1_pre_topc(C_1113,D_1115) != g1_pre_topc(A_1114,B_1116)
      | ~ m1_subset_1(B_1116,k1_zfmisc_1(k1_zfmisc_1(A_1114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41592,plain,(
    ! [A_1,C_1113,D_1115] :
      ( u1_struct_0(A_1) = C_1113
      | g1_pre_topc(C_1113,D_1115) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_41588])).

tff(c_42620,plain,(
    ! [C_1161,D_1162] :
      ( u1_struct_0(g1_pre_topc(C_1161,D_1162)) = C_1161
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_1161,D_1162)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1161,D_1162)))))
      | ~ v1_pre_topc(g1_pre_topc(C_1161,D_1162))
      | ~ l1_pre_topc(g1_pre_topc(C_1161,D_1162)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_41592])).

tff(c_42638,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41841,c_42620])).

tff(c_42653,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_42517,c_41884,c_42638])).

tff(c_42657,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42653,c_41558])).

tff(c_42659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42068,c_42657])).

tff(c_42661,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_42052])).

tff(c_42664,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42661,c_32])).

tff(c_42678,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_42664])).

tff(c_42679,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_41549,c_42678])).

tff(c_42692,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42679])).

tff(c_42670,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42661,c_26])).

tff(c_42685,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42670])).

tff(c_42660,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_42052])).

tff(c_42761,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42685,c_42660])).

tff(c_42947,plain,(
    ! [C_1165,D_1166] :
      ( u1_struct_0(g1_pre_topc(C_1165,D_1166)) = C_1165
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_1165,D_1166)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1165,D_1166)))))
      | ~ v1_pre_topc(g1_pre_topc(C_1165,D_1166))
      | ~ l1_pre_topc(g1_pre_topc(C_1165,D_1166)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_41592])).

tff(c_42965,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41841,c_42947])).

tff(c_42980,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_41884,c_42965])).

tff(c_43010,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_42980])).

tff(c_43016,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_43010])).

tff(c_43022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_43016])).

tff(c_43023,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_42980])).

tff(c_42675,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42661,c_14])).

tff(c_42691,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42675])).

tff(c_42672,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42661,c_12])).

tff(c_42688,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42672])).

tff(c_42747,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42688,c_6])).

tff(c_42750,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42661,c_42691,c_42747])).

tff(c_42754,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42750,c_4])).

tff(c_43458,plain,(
    ! [A_1177] :
      ( k1_pre_topc(A_1177,'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_1177)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1177)))
      | ~ l1_pre_topc(A_1177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42691,c_42750,c_42754])).

tff(c_43467,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43023,c_43458])).

tff(c_43478,plain,
    ( g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_42661,c_42761,c_43467])).

tff(c_43803,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_43478])).

tff(c_41571,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_41558,c_12])).

tff(c_41765,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_41571])).

tff(c_41768,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_41765,c_28])).

tff(c_41777,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_41768])).

tff(c_42764,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42761,c_41777])).

tff(c_41609,plain,(
    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_41572])).

tff(c_42768,plain,(
    v1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42761,c_41609])).

tff(c_41787,plain,(
    ! [A_1141,B_1142] :
      ( k2_struct_0(k1_pre_topc(A_1141,B_1142)) = B_1142
      | ~ m1_pre_topc(k1_pre_topc(A_1141,B_1142),A_1141)
      | ~ v1_pre_topc(k1_pre_topc(A_1141,B_1142))
      | ~ m1_subset_1(B_1142,k1_zfmisc_1(u1_struct_0(A_1141)))
      | ~ l1_pre_topc(A_1141) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41789,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_41765,c_41787])).

tff(c_41792,plain,(
    k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_41558,c_41609,c_41789])).

tff(c_42763,plain,(
    k2_struct_0(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42761,c_41792])).

tff(c_42838,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))))) = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),A_2)
      | ~ v1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42763,c_4])).

tff(c_45286,plain,(
    ! [A_1229] :
      ( k1_pre_topc(A_1229,'#skF_2') = g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))
      | ~ m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),A_1229)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1229)))
      | ~ l1_pre_topc(A_1229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42768,c_42763,c_42838])).

tff(c_45292,plain,
    ( g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42764,c_45286])).

tff(c_45298,plain,(
    g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42661,c_45292])).

tff(c_42765,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42761,c_41765])).

tff(c_45306,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45298,c_42765])).

tff(c_45315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43803,c_45306])).

tff(c_45316,plain,(
    g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_43478])).

tff(c_41522,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_41616,plain,(
    ! [A_1119,B_1120] :
      ( v1_compts_1(k1_pre_topc(A_1119,B_1120))
      | ~ v2_compts_1(B_1120,A_1119)
      | k1_xboole_0 = B_1120
      | ~ v2_pre_topc(A_1119)
      | ~ m1_subset_1(B_1120,k1_zfmisc_1(u1_struct_0(A_1119)))
      | ~ l1_pre_topc(A_1119) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_41619,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_41558,c_41616])).

tff(c_41622,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_41522,c_41619])).

tff(c_41676,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_41622])).

tff(c_41683,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_41676])).

tff(c_41689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_41683])).

tff(c_41690,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_41622])).

tff(c_41697,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_41690])).

tff(c_42766,plain,(
    v1_compts_1(g1_pre_topc('#skF_2',u1_pre_topc(k1_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42761,c_41697])).

tff(c_45321,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45316,c_42766])).

tff(c_45329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42692,c_45321])).

tff(c_45331,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42679])).

tff(c_45330,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42679])).

tff(c_45612,plain,(
    ! [A_1233] :
      ( v2_compts_1('#skF_2',A_1233)
      | ~ v1_compts_1(k1_pre_topc(A_1233,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1233)))
      | ~ l1_pre_topc(A_1233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45330,c_45330,c_45330,c_36])).

tff(c_45621,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42661,c_45612])).

tff(c_45627,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45331,c_45621])).

tff(c_45629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41549,c_45627])).

tff(c_45631,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_41690])).

tff(c_45630,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_41690])).

tff(c_45644,plain,(
    ! [A_1234] :
      ( v1_compts_1(k1_pre_topc(A_1234,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_1234)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1234)))
      | ~ l1_pre_topc(A_1234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45630,c_45630,c_45630,c_38])).

tff(c_45650,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_41558,c_45644])).

tff(c_45653,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41610,c_41522,c_45650])).

tff(c_45655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45631,c_45653])).

tff(c_45656,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_41548])).

tff(c_45661,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_41523,c_60])).

tff(c_45671,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_45661,c_14])).

tff(c_45707,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_45671])).

tff(c_45713,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_45707])).

tff(c_45719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45713])).

tff(c_45721,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_45671])).

tff(c_45700,plain,(
    ! [D_1247,B_1248,C_1249,A_1250] :
      ( D_1247 = B_1248
      | g1_pre_topc(C_1249,D_1247) != g1_pre_topc(A_1250,B_1248)
      | ~ m1_subset_1(B_1248,k1_zfmisc_1(k1_zfmisc_1(A_1250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45702,plain,(
    ! [A_1,B_1248,A_1250] :
      ( u1_pre_topc(A_1) = B_1248
      | g1_pre_topc(A_1250,B_1248) != A_1
      | ~ m1_subset_1(B_1248,k1_zfmisc_1(k1_zfmisc_1(A_1250)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_45700])).

tff(c_45866,plain,(
    ! [A_1271,B_1272] :
      ( u1_pre_topc(g1_pre_topc(A_1271,B_1272)) = B_1272
      | ~ m1_subset_1(B_1272,k1_zfmisc_1(k1_zfmisc_1(A_1271)))
      | ~ v1_pre_topc(g1_pre_topc(A_1271,B_1272))
      | ~ l1_pre_topc(g1_pre_topc(A_1271,B_1272)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_45702])).

tff(c_45926,plain,(
    ! [A_1277] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1277),u1_pre_topc(A_1277))) = u1_pre_topc(A_1277)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1277),u1_pre_topc(A_1277)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1277),u1_pre_topc(A_1277)))
      | ~ l1_pre_topc(A_1277) ) ),
    inference(resolution,[status(thm)],[c_16,c_45866])).

tff(c_45949,plain,(
    ! [A_1280] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1280),u1_pre_topc(A_1280))) = u1_pre_topc(A_1280)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1280),u1_pre_topc(A_1280)))
      | ~ l1_pre_topc(A_1280) ) ),
    inference(resolution,[status(thm)],[c_68,c_45926])).

tff(c_45955,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_45721,c_45949])).

tff(c_45965,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45955])).

tff(c_45990,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_45965,c_16])).

tff(c_46011,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45721,c_45990])).

tff(c_45690,plain,(
    ! [C_1243,A_1244,D_1245,B_1246] :
      ( C_1243 = A_1244
      | g1_pre_topc(C_1243,D_1245) != g1_pre_topc(A_1244,B_1246)
      | ~ m1_subset_1(B_1246,k1_zfmisc_1(k1_zfmisc_1(A_1244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45694,plain,(
    ! [A_1,C_1243,D_1245] :
      ( u1_struct_0(A_1) = C_1243
      | g1_pre_topc(C_1243,D_1245) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_45690])).

tff(c_46405,plain,(
    ! [C_1284,D_1285] :
      ( u1_struct_0(g1_pre_topc(C_1284,D_1285)) = C_1284
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_1284,D_1285)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1284,D_1285)))))
      | ~ v1_pre_topc(g1_pre_topc(C_1284,D_1285))
      | ~ l1_pre_topc(g1_pre_topc(C_1284,D_1285)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_45694])).

tff(c_46423,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_45965,c_46405])).

tff(c_46438,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45721,c_46011,c_46423])).

tff(c_46457,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_46438])).

tff(c_46463,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_46457])).

tff(c_46469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_46463])).

tff(c_46470,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_46438])).

tff(c_46490,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46470,c_45661])).

tff(c_46496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45656,c_46490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.38/9.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.64/9.43  
% 19.64/9.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.64/9.44  %$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 19.64/9.44  
% 19.64/9.44  %Foreground sorts:
% 19.64/9.44  
% 19.64/9.44  
% 19.64/9.44  %Background operators:
% 19.64/9.44  
% 19.64/9.44  
% 19.64/9.44  %Foreground operators:
% 19.64/9.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.64/9.44  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 19.64/9.44  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 19.64/9.44  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 19.64/9.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.64/9.44  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 19.64/9.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.64/9.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.64/9.44  tff('#skF_2', type, '#skF_2': $i).
% 19.64/9.44  tff('#skF_3', type, '#skF_3': $i).
% 19.64/9.44  tff('#skF_1', type, '#skF_1': $i).
% 19.64/9.44  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 19.64/9.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.64/9.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.64/9.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.64/9.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 19.64/9.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.64/9.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.64/9.44  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 19.64/9.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 19.64/9.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.64/9.44  
% 20.06/9.49  tff(f_142, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_compts_1(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v2_compts_1(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_compts_1)).
% 20.06/9.49  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 20.06/9.49  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 20.06/9.49  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 20.06/9.49  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 20.06/9.49  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 20.06/9.49  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 20.06/9.49  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))) => ((B = C) => (g1_pre_topc(u1_struct_0(k1_pre_topc(A, B)), u1_pre_topc(k1_pre_topc(A, B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_pre_topc)).
% 20.06/9.49  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 20.06/9.49  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 20.06/9.49  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 20.06/9.49  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 20.06/9.49  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_62, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_77, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 20.06/9.49  tff(c_56, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_56])).
% 20.06/9.49  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_222, plain, (![A_75, B_76]: (v1_compts_1(k1_pre_topc(A_75, B_76)) | ~v2_compts_1(B_76, A_75) | k1_xboole_0=B_76 | ~v2_pre_topc(A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.06/9.49  tff(c_228, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_222])).
% 20.06/9.49  tff(c_231, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_77, c_228])).
% 20.06/9.49  tff(c_232, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_231])).
% 20.06/9.49  tff(c_38, plain, (![A_34]: (v1_compts_1(k1_pre_topc(A_34, k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, A_34) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.06/9.49  tff(c_241, plain, (![A_77]: (v1_compts_1(k1_pre_topc(A_77, '#skF_3')) | ~v2_compts_1('#skF_3', A_77) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_232, c_232, c_38])).
% 20.06/9.49  tff(c_247, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_241])).
% 20.06/9.49  tff(c_250, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_77, c_247])).
% 20.06/9.49  tff(c_16, plain, (![A_13]: (m1_subset_1(u1_pre_topc(A_13), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.06/9.49  tff(c_69, plain, (![A_41, B_42]: (l1_pre_topc(g1_pre_topc(A_41, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.06/9.49  tff(c_73, plain, (![A_13]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_13), u1_pre_topc(A_13))) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_16, c_69])).
% 20.06/9.49  tff(c_105, plain, (![A_49, B_50]: (u1_struct_0(k1_pre_topc(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.06/9.49  tff(c_108, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_105])).
% 20.06/9.49  tff(c_111, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_108])).
% 20.06/9.49  tff(c_64, plain, (![A_39, B_40]: (v1_pre_topc(g1_pre_topc(A_39, B_40)) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.06/9.49  tff(c_68, plain, (![A_13]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_13), u1_pre_topc(A_13))) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_16, c_64])).
% 20.06/9.49  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.06/9.49  tff(c_170, plain, (![C_59, A_60, D_61, B_62]: (C_59=A_60 | g1_pre_topc(C_59, D_61)!=g1_pre_topc(A_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_172, plain, (![A_1, A_60, B_62]: (u1_struct_0(A_1)=A_60 | g1_pre_topc(A_60, B_62)!=A_1 | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_60))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_170])).
% 20.06/9.49  tff(c_321, plain, (![A_93, B_94]: (u1_struct_0(g1_pre_topc(A_93, B_94))=A_93 | ~m1_subset_1(B_94, k1_zfmisc_1(k1_zfmisc_1(A_93))) | ~v1_pre_topc(g1_pre_topc(A_93, B_94)) | ~l1_pre_topc(g1_pre_topc(A_93, B_94)))), inference(reflexivity, [status(thm), theory('equality')], [c_172])).
% 20.06/9.49  tff(c_467, plain, (![A_104]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_104), u1_pre_topc(A_104)))=u1_struct_0(A_104) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_104), u1_pre_topc(A_104))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_104), u1_pre_topc(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_16, c_321])).
% 20.06/9.49  tff(c_482, plain, (![A_105]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105)))=u1_struct_0(A_105) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_68, c_467])).
% 20.06/9.49  tff(c_497, plain, (![A_106]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106)))=u1_struct_0(A_106) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_73, c_482])).
% 20.06/9.49  tff(c_30, plain, (![A_27, C_33]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_27, C_33)), u1_pre_topc(k1_pre_topc(A_27, C_33)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_27), u1_pre_topc(A_27)), C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_27), u1_pre_topc(A_27))))) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_106])).
% 20.06/9.49  tff(c_2465, plain, (![A_157, C_158]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_157, C_158)), u1_pre_topc(k1_pre_topc(A_157, C_158)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_157), u1_pre_topc(A_157)), C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~l1_pre_topc(A_157))), inference(superposition, [status(thm), theory('equality')], [c_497, c_30])).
% 20.06/9.49  tff(c_2621, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111, c_2465])).
% 20.06/9.49  tff(c_2628, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_98, c_98, c_2621])).
% 20.06/9.49  tff(c_14, plain, (![A_11, B_12]: (v1_pre_topc(k1_pre_topc(A_11, B_12)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.06/9.49  tff(c_557, plain, (![A_106, B_12]: (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106)), B_12)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106))) | ~l1_pre_topc(A_106))), inference(superposition, [status(thm), theory('equality')], [c_497, c_14])).
% 20.06/9.49  tff(c_2668, plain, (v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2628, c_557])).
% 20.06/9.49  tff(c_2698, plain, (v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_2668])).
% 20.06/9.49  tff(c_2746, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2698])).
% 20.06/9.49  tff(c_2752, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_2746])).
% 20.06/9.49  tff(c_2758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2752])).
% 20.06/9.49  tff(c_2760, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2698])).
% 20.06/9.49  tff(c_12, plain, (![A_11, B_12]: (m1_pre_topc(k1_pre_topc(A_11, B_12), A_11) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.06/9.49  tff(c_1699, plain, (![A_135, B_136]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135)), B_136), g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))) | ~l1_pre_topc(A_135))), inference(superposition, [status(thm), theory('equality')], [c_497, c_12])).
% 20.06/9.49  tff(c_1761, plain, (![A_1, B_136]: (m1_pre_topc(k1_pre_topc(A_1, B_136), g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))) | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1699])).
% 20.06/9.49  tff(c_2650, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2628, c_1761])).
% 20.06/9.49  tff(c_3138, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_2760, c_2650])).
% 20.06/9.49  tff(c_3139, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_3138])).
% 20.06/9.49  tff(c_3145, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_3139])).
% 20.06/9.49  tff(c_3151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3145])).
% 20.06/9.49  tff(c_3153, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_3138])).
% 20.06/9.49  tff(c_174, plain, (![A_1, C_59, D_61]: (u1_struct_0(A_1)=C_59 | g1_pre_topc(C_59, D_61)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_170])).
% 20.06/9.49  tff(c_949, plain, (![C_121, D_122]: (u1_struct_0(g1_pre_topc(C_121, D_122))=C_121 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_121, D_122)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_121, D_122))))) | ~v1_pre_topc(g1_pre_topc(C_121, D_122)) | ~l1_pre_topc(g1_pre_topc(C_121, D_122)))), inference(reflexivity, [status(thm), theory('equality')], [c_174])).
% 20.06/9.49  tff(c_971, plain, (![C_121, D_122]: (u1_struct_0(g1_pre_topc(C_121, D_122))=C_121 | ~v1_pre_topc(g1_pre_topc(C_121, D_122)) | ~l1_pre_topc(g1_pre_topc(C_121, D_122)))), inference(resolution, [status(thm)], [c_16, c_949])).
% 20.06/9.49  tff(c_3156, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_3153, c_971])).
% 20.06/9.49  tff(c_3165, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_3156])).
% 20.06/9.49  tff(c_101, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_14])).
% 20.06/9.49  tff(c_104, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_101])).
% 20.06/9.49  tff(c_141, plain, (![A_51, B_52]: (m1_pre_topc(k1_pre_topc(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.06/9.49  tff(c_145, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_141])).
% 20.06/9.49  tff(c_148, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_145])).
% 20.06/9.49  tff(c_290, plain, (![A_87, B_88]: (k2_struct_0(k1_pre_topc(A_87, B_88))=B_88 | ~m1_pre_topc(k1_pre_topc(A_87, B_88), A_87) | ~v1_pre_topc(k1_pre_topc(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.06/9.49  tff(c_292, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_148, c_290])).
% 20.06/9.49  tff(c_295, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_104, c_292])).
% 20.06/9.49  tff(c_4, plain, (![A_2, C_8]: (k1_pre_topc(A_2, k2_struct_0(C_8))=C_8 | ~m1_pre_topc(C_8, A_2) | ~v1_pre_topc(C_8) | ~m1_subset_1(k2_struct_0(C_8), k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.06/9.49  tff(c_299, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_295, c_4])).
% 20.06/9.49  tff(c_303, plain, (![A_2]: (k1_pre_topc(A_2, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_295, c_299])).
% 20.06/9.49  tff(c_3347, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3165, c_303])).
% 20.06/9.49  tff(c_3518, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_98, c_2628, c_3347])).
% 20.06/9.49  tff(c_4319, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_3518])).
% 20.06/9.49  tff(c_28, plain, (![B_26, A_24]: (m1_pre_topc(B_26, A_24) | ~m1_pre_topc(B_26, g1_pre_topc(u1_struct_0(A_24), u1_pre_topc(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.06/9.49  tff(c_1766, plain, (![A_135, B_136]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135)), B_136), A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_1699, c_28])).
% 20.06/9.49  tff(c_2653, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2628, c_1766])).
% 20.06/9.49  tff(c_2688, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), '#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_2653])).
% 20.06/9.49  tff(c_2777, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_2688])).
% 20.06/9.49  tff(c_2759, plain, (v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))))), inference(splitRight, [status(thm)], [c_2698])).
% 20.06/9.49  tff(c_551, plain, (![A_106, B_12]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106)), B_12), g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106))) | ~l1_pre_topc(A_106))), inference(superposition, [status(thm), theory('equality')], [c_497, c_12])).
% 20.06/9.49  tff(c_2656, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2628, c_551])).
% 20.06/9.49  tff(c_2690, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_2656])).
% 20.06/9.49  tff(c_3125, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_2690])).
% 20.06/9.49  tff(c_6, plain, (![A_2, B_6]: (k2_struct_0(k1_pre_topc(A_2, B_6))=B_6 | ~m1_pre_topc(k1_pre_topc(A_2, B_6), A_2) | ~v1_pre_topc(k1_pre_topc(A_2, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.06/9.49  tff(c_2670, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'))='#skF_3' | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2628, c_6])).
% 20.06/9.49  tff(c_2699, plain, (k2_struct_0(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))))='#skF_3' | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2628, c_2628, c_2670])).
% 20.06/9.49  tff(c_4309, plain, (k2_struct_0(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_98, c_3165, c_2759, c_3125, c_2699])).
% 20.06/9.49  tff(c_4313, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))))=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))) | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), A_2) | ~v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_4309, c_4])).
% 20.06/9.49  tff(c_6110, plain, (![A_223]: (k1_pre_topc(A_223, '#skF_3')=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))) | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), A_223) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_2759, c_4309, c_4313])).
% 20.06/9.49  tff(c_6116, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2777, c_6110])).
% 20.06/9.49  tff(c_6122, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_6116])).
% 20.06/9.49  tff(c_6198, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6122, c_3125])).
% 20.06/9.49  tff(c_6207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4319, c_6198])).
% 20.06/9.49  tff(c_6208, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_3518])).
% 20.06/9.49  tff(c_50, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_188, plain, (~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_50])).
% 20.06/9.49  tff(c_36, plain, (![A_34]: (v2_compts_1(k1_xboole_0, A_34) | ~v1_compts_1(k1_pre_topc(A_34, k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.06/9.49  tff(c_236, plain, (![A_34]: (v2_compts_1('#skF_3', A_34) | ~v1_compts_1(k1_pre_topc(A_34, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_232, c_232, c_36])).
% 20.06/9.49  tff(c_540, plain, (![A_106]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106)), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106))) | ~l1_pre_topc(A_106))), inference(superposition, [status(thm), theory('equality')], [c_497, c_236])).
% 20.06/9.49  tff(c_2641, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2628, c_540])).
% 20.06/9.49  tff(c_2681, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_2641])).
% 20.06/9.49  tff(c_2682, plain, (~v1_compts_1(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_188, c_2681])).
% 20.06/9.49  tff(c_2767, plain, (~v1_compts_1(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_2682])).
% 20.06/9.49  tff(c_6216, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6208, c_2767])).
% 20.06/9.49  tff(c_6224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_6216])).
% 20.06/9.49  tff(c_6226, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_231])).
% 20.06/9.49  tff(c_6225, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_231])).
% 20.06/9.49  tff(c_6243, plain, (![A_233, B_234]: (u1_struct_0(g1_pre_topc(A_233, B_234))=A_233 | ~m1_subset_1(B_234, k1_zfmisc_1(k1_zfmisc_1(A_233))) | ~v1_pre_topc(g1_pre_topc(A_233, B_234)) | ~l1_pre_topc(g1_pre_topc(A_233, B_234)))), inference(reflexivity, [status(thm), theory('equality')], [c_172])).
% 20.06/9.49  tff(c_6279, plain, (![A_240]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240)))=u1_struct_0(A_240) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))) | ~l1_pre_topc(A_240))), inference(resolution, [status(thm)], [c_16, c_6243])).
% 20.06/9.49  tff(c_6291, plain, (![A_241]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_241), u1_pre_topc(A_241)))=u1_struct_0(A_241) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_241), u1_pre_topc(A_241))) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_68, c_6279])).
% 20.06/9.49  tff(c_6302, plain, (![A_13]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_13), u1_pre_topc(A_13)))=u1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_73, c_6291])).
% 20.06/9.49  tff(c_6406, plain, (![A_245, C_246]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_245, C_246)), u1_pre_topc(k1_pre_topc(A_245, C_246)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_245), u1_pre_topc(A_245)), C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_245), u1_pre_topc(A_245))))) | ~m1_subset_1(C_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_106])).
% 20.06/9.49  tff(c_8460, plain, (![A_303, C_304]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_303, C_304)), u1_pre_topc(k1_pre_topc(A_303, C_304)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_303), u1_pre_topc(A_303)), C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(u1_struct_0(A_303))) | ~m1_subset_1(C_304, k1_zfmisc_1(u1_struct_0(A_303))) | ~l1_pre_topc(A_303) | ~l1_pre_topc(A_303))), inference(superposition, [status(thm), theory('equality')], [c_6302, c_6406])).
% 20.06/9.49  tff(c_8621, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111, c_8460])).
% 20.06/9.49  tff(c_8629, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_98, c_98, c_8621])).
% 20.06/9.49  tff(c_6303, plain, (![A_242]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242)))=u1_struct_0(A_242) | ~l1_pre_topc(A_242))), inference(resolution, [status(thm)], [c_73, c_6291])).
% 20.06/9.49  tff(c_6338, plain, (![A_242, B_12]: (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242)), B_12)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))) | ~l1_pre_topc(A_242))), inference(superposition, [status(thm), theory('equality')], [c_6303, c_14])).
% 20.06/9.49  tff(c_8666, plain, (v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8629, c_6338])).
% 20.06/9.49  tff(c_8696, plain, (v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_8666])).
% 20.06/9.49  tff(c_8703, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_8696])).
% 20.06/9.49  tff(c_8755, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_8703])).
% 20.06/9.49  tff(c_8761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_8755])).
% 20.06/9.49  tff(c_8763, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_8696])).
% 20.06/9.49  tff(c_7824, plain, (![A_285, B_286]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_285), u1_pre_topc(A_285)), B_286), g1_pre_topc(u1_struct_0(A_285), u1_pre_topc(A_285))) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_285), u1_pre_topc(A_285))) | ~l1_pre_topc(A_285))), inference(superposition, [status(thm), theory('equality')], [c_6303, c_12])).
% 20.06/9.49  tff(c_7889, plain, (![A_1, B_286]: (m1_pre_topc(k1_pre_topc(A_1, B_286), g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))) | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7824])).
% 20.06/9.49  tff(c_8642, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8629, c_7889])).
% 20.06/9.49  tff(c_8778, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_8763, c_8642])).
% 20.06/9.49  tff(c_8779, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_8778])).
% 20.06/9.49  tff(c_8785, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_8779])).
% 20.06/9.49  tff(c_8791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_8785])).
% 20.06/9.49  tff(c_8793, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_8778])).
% 20.06/9.49  tff(c_6874, plain, (![C_262, D_263]: (u1_struct_0(g1_pre_topc(C_262, D_263))=C_262 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_262, D_263)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_262, D_263))))) | ~v1_pre_topc(g1_pre_topc(C_262, D_263)) | ~l1_pre_topc(g1_pre_topc(C_262, D_263)))), inference(reflexivity, [status(thm), theory('equality')], [c_174])).
% 20.06/9.49  tff(c_6896, plain, (![C_262, D_263]: (u1_struct_0(g1_pre_topc(C_262, D_263))=C_262 | ~v1_pre_topc(g1_pre_topc(C_262, D_263)) | ~l1_pre_topc(g1_pre_topc(C_262, D_263)))), inference(resolution, [status(thm)], [c_16, c_6874])).
% 20.06/9.49  tff(c_8799, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_8793, c_6896])).
% 20.06/9.49  tff(c_8808, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_8799])).
% 20.06/9.49  tff(c_128, plain, (l1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_73])).
% 20.06/9.49  tff(c_140, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_128])).
% 20.06/9.49  tff(c_6253, plain, (![A_237, B_238]: (k2_struct_0(k1_pre_topc(A_237, B_238))=B_238 | ~m1_pre_topc(k1_pre_topc(A_237, B_238), A_237) | ~v1_pre_topc(k1_pre_topc(A_237, B_238)) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_237))) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.06/9.49  tff(c_6255, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_148, c_6253])).
% 20.06/9.49  tff(c_6258, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_104, c_6255])).
% 20.06/9.49  tff(c_6262, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_6258, c_4])).
% 20.06/9.49  tff(c_6266, plain, (![A_2]: (k1_pre_topc(A_2, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_6258, c_6262])).
% 20.06/9.49  tff(c_6476, plain, (![A_251]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_251), u1_pre_topc(A_251)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0(A_251), u1_pre_topc(A_251))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_251), u1_pre_topc(A_251))) | ~l1_pre_topc(A_251))), inference(superposition, [status(thm), theory('equality')], [c_6303, c_6266])).
% 20.06/9.49  tff(c_6730, plain, (![A_259]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_259), u1_pre_topc(A_259)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_259) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_259), u1_pre_topc(A_259))) | ~l1_pre_topc(A_259) | ~v1_pre_topc(A_259) | ~l1_pre_topc(A_259))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6476])).
% 20.06/9.49  tff(c_7711, plain, (![A_282]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_282) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_282))) | ~v1_pre_topc(A_282) | ~l1_pre_topc(A_282))), inference(resolution, [status(thm)], [c_73, c_6730])).
% 20.06/9.49  tff(c_6614, plain, (![A_256, C_257]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_256, C_257)), u1_pre_topc(k1_pre_topc(A_256, C_257)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_256), u1_pre_topc(A_256)), C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256) | ~v1_pre_topc(A_256) | ~l1_pre_topc(A_256))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6406])).
% 20.06/9.49  tff(c_6674, plain, (![A_256, C_257]: (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_256), u1_pre_topc(A_256)), C_257)) | ~l1_pre_topc(k1_pre_topc(A_256, C_257)) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256) | ~v1_pre_topc(A_256) | ~l1_pre_topc(A_256))), inference(superposition, [status(thm), theory('equality')], [c_6614, c_73])).
% 20.06/9.49  tff(c_7723, plain, (![A_282]: (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc(A_282, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~v1_pre_topc(A_282) | ~l1_pre_topc(A_282) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_282) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_282))) | ~v1_pre_topc(A_282) | ~l1_pre_topc(A_282))), inference(superposition, [status(thm), theory('equality')], [c_7711, c_6674])).
% 20.06/9.49  tff(c_7773, plain, (![A_282]: (~l1_pre_topc(k1_pre_topc(A_282, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~v1_pre_topc(A_282) | ~l1_pre_topc(A_282) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_282) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_282))) | ~v1_pre_topc(A_282) | ~l1_pre_topc(A_282))), inference(negUnitSimplification, [status(thm)], [c_140, c_7723])).
% 20.06/9.49  tff(c_9178, plain, (~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8808, c_7773])).
% 20.06/9.49  tff(c_9381, plain, (~l1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_8793, c_98, c_8808, c_8763, c_8793, c_8763, c_98, c_8808, c_98, c_8629, c_9178])).
% 20.06/9.49  tff(c_10126, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_9381])).
% 20.06/9.49  tff(c_7894, plain, (![A_285, B_286]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_285), u1_pre_topc(A_285)), B_286), A_285) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_285), u1_pre_topc(A_285))) | ~l1_pre_topc(A_285))), inference(resolution, [status(thm)], [c_7824, c_28])).
% 20.06/9.49  tff(c_8645, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8629, c_7894])).
% 20.06/9.49  tff(c_8682, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), '#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_8645])).
% 20.06/9.49  tff(c_9880, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_8682])).
% 20.06/9.49  tff(c_8762, plain, (v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))))), inference(splitRight, [status(thm)], [c_8696])).
% 20.06/9.49  tff(c_6332, plain, (![A_242, B_12]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242)), B_12), g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))) | ~l1_pre_topc(A_242))), inference(superposition, [status(thm), theory('equality')], [c_6303, c_12])).
% 20.06/9.49  tff(c_8648, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8629, c_6332])).
% 20.06/9.49  tff(c_8684, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_8648])).
% 20.06/9.49  tff(c_10112, plain, (m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_8684])).
% 20.06/9.49  tff(c_8668, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'))='#skF_3' | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8629, c_6])).
% 20.06/9.49  tff(c_8697, plain, (k2_struct_0(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))))='#skF_3' | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8629, c_8629, c_8668])).
% 20.06/9.49  tff(c_10325, plain, (k2_struct_0(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_98, c_8808, c_8762, c_10112, c_8697])).
% 20.06/9.49  tff(c_10329, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))))=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))) | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), A_2) | ~v1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_10325, c_4])).
% 20.06/9.49  tff(c_12390, plain, (![A_375]: (k1_pre_topc(A_375, '#skF_3')=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))) | ~m1_pre_topc(g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), A_375) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_pre_topc(A_375))), inference(demodulation, [status(thm), theory('equality')], [c_8762, c_10325, c_10329])).
% 20.06/9.49  tff(c_12396, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_9880, c_12390])).
% 20.06/9.49  tff(c_12402, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_12396])).
% 20.06/9.49  tff(c_12489, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12402, c_10112])).
% 20.06/9.49  tff(c_12496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10126, c_12489])).
% 20.06/9.49  tff(c_12498, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_9381])).
% 20.06/9.49  tff(c_6312, plain, (![A_242]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))) | ~l1_pre_topc(A_242))), inference(superposition, [status(thm), theory('equality')], [c_6303, c_6266])).
% 20.06/9.49  tff(c_12501, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12498, c_6312])).
% 20.06/9.49  tff(c_12510, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8763, c_98, c_8629, c_12501])).
% 20.06/9.49  tff(c_12521, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12510, c_8629])).
% 20.06/9.49  tff(c_18, plain, (![A_14]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_14), u1_pre_topc(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.06/9.49  tff(c_34, plain, (![A_34, B_36]: (v1_compts_1(k1_pre_topc(A_34, B_36)) | ~v2_compts_1(B_36, A_34) | k1_xboole_0=B_36 | ~v2_pre_topc(A_34) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.06/9.49  tff(c_9302, plain, (![B_36]: (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_36)) | ~v2_compts_1(B_36, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0=B_36 | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_8808, c_34])).
% 20.06/9.49  tff(c_9466, plain, (![B_36]: (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_36)) | ~v2_compts_1(B_36, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0=B_36 | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_9302])).
% 20.06/9.49  tff(c_23361, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_9466])).
% 20.06/9.49  tff(c_23367, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_23361])).
% 20.06/9.49  tff(c_23373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_23367])).
% 20.06/9.49  tff(c_23375, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_9466])).
% 20.06/9.49  tff(c_32, plain, (![B_36, A_34]: (v2_compts_1(B_36, A_34) | ~v1_compts_1(k1_pre_topc(A_34, B_36)) | k1_xboole_0=B_36 | ~v2_pre_topc(A_34) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.06/9.49  tff(c_9305, plain, (![B_36]: (v2_compts_1(B_36, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_36)) | k1_xboole_0=B_36 | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_8808, c_32])).
% 20.06/9.49  tff(c_9468, plain, (![B_36]: (v2_compts_1(B_36, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_36)) | k1_xboole_0=B_36 | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_8763, c_9305])).
% 20.06/9.49  tff(c_23426, plain, (![B_577]: (v2_compts_1(B_577, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_577)) | k1_xboole_0=B_577 | ~m1_subset_1(B_577, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_23375, c_9468])).
% 20.06/9.49  tff(c_23441, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12521, c_23426])).
% 20.06/9.49  tff(c_23459, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_6225, c_23441])).
% 20.06/9.49  tff(c_23461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6226, c_188, c_23459])).
% 20.06/9.49  tff(c_23463, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 20.06/9.49  tff(c_23608, plain, (![A_606, B_607]: (u1_struct_0(g1_pre_topc(A_606, B_607))=A_606 | ~m1_subset_1(B_607, k1_zfmisc_1(k1_zfmisc_1(A_606))) | ~v1_pre_topc(g1_pre_topc(A_606, B_607)) | ~l1_pre_topc(g1_pre_topc(A_606, B_607)))), inference(reflexivity, [status(thm), theory('equality')], [c_172])).
% 20.06/9.49  tff(c_23810, plain, (![A_617]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_617), u1_pre_topc(A_617)))=u1_struct_0(A_617) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_617), u1_pre_topc(A_617))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_617), u1_pre_topc(A_617))) | ~l1_pre_topc(A_617))), inference(resolution, [status(thm)], [c_16, c_23608])).
% 20.06/9.49  tff(c_23828, plain, (![A_618]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_618), u1_pre_topc(A_618)))=u1_struct_0(A_618) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_618), u1_pre_topc(A_618))) | ~l1_pre_topc(A_618))), inference(resolution, [status(thm)], [c_68, c_23810])).
% 20.06/9.49  tff(c_23846, plain, (![A_619]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_619), u1_pre_topc(A_619)))=u1_struct_0(A_619) | ~l1_pre_topc(A_619))), inference(resolution, [status(thm)], [c_73, c_23828])).
% 20.06/9.49  tff(c_23462, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 20.06/9.49  tff(c_23469, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_23462])).
% 20.06/9.49  tff(c_23895, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23846, c_23469])).
% 20.06/9.49  tff(c_23946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_98, c_23895])).
% 20.06/9.49  tff(c_23948, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_23462])).
% 20.06/9.49  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_23992, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23463, c_23948, c_46])).
% 20.06/9.49  tff(c_23993, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_23992])).
% 20.06/9.49  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_27327, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_23463, c_23948, c_48])).
% 20.06/9.49  tff(c_27625, plain, (![A_719, C_720]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_719, C_720)), u1_pre_topc(k1_pre_topc(A_719, C_720)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_719), u1_pre_topc(A_719)), C_720) | ~m1_subset_1(C_720, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_719), u1_pre_topc(A_719))))) | ~m1_subset_1(C_720, k1_zfmisc_1(u1_struct_0(A_719))) | ~l1_pre_topc(A_719))), inference(cnfTransformation, [status(thm)], [f_106])).
% 20.06/9.49  tff(c_27629, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27327, c_27625])).
% 20.06/9.49  tff(c_27641, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27629])).
% 20.06/9.49  tff(c_27666, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_27641])).
% 20.06/9.49  tff(c_23968, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_23948, c_14])).
% 20.06/9.49  tff(c_23971, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_23968])).
% 20.06/9.49  tff(c_23977, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_23971])).
% 20.06/9.49  tff(c_23983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_23977])).
% 20.06/9.49  tff(c_23985, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_23968])).
% 20.06/9.49  tff(c_27597, plain, (![A_716, B_717]: (u1_struct_0(g1_pre_topc(A_716, B_717))=A_716 | ~m1_subset_1(B_717, k1_zfmisc_1(k1_zfmisc_1(A_716))) | ~v1_pre_topc(g1_pre_topc(A_716, B_717)) | ~l1_pre_topc(g1_pre_topc(A_716, B_717)))), inference(reflexivity, [status(thm), theory('equality')], [c_172])).
% 20.06/9.49  tff(c_27817, plain, (![A_723]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_723), u1_pre_topc(A_723)))=u1_struct_0(A_723) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_723), u1_pre_topc(A_723))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_723), u1_pre_topc(A_723))) | ~l1_pre_topc(A_723))), inference(resolution, [status(thm)], [c_16, c_27597])).
% 20.06/9.49  tff(c_27841, plain, (![A_724]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_724), u1_pre_topc(A_724)))=u1_struct_0(A_724) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_724), u1_pre_topc(A_724))) | ~l1_pre_topc(A_724))), inference(resolution, [status(thm)], [c_68, c_27817])).
% 20.06/9.49  tff(c_27853, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_23985, c_27841])).
% 20.06/9.49  tff(c_27867, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27853])).
% 20.06/9.49  tff(c_27870, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_27867, c_27327])).
% 20.06/9.49  tff(c_27873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27666, c_27870])).
% 20.06/9.49  tff(c_27875, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_27641])).
% 20.06/9.49  tff(c_27881, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27875, c_32])).
% 20.06/9.49  tff(c_27895, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_27881])).
% 20.06/9.49  tff(c_27896, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_23993, c_27895])).
% 20.06/9.49  tff(c_27964, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_27896])).
% 20.06/9.49  tff(c_26, plain, (![A_21, B_23]: (u1_struct_0(k1_pre_topc(A_21, B_23))=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.06/9.49  tff(c_27886, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27875, c_26])).
% 20.06/9.49  tff(c_27902, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27886])).
% 20.06/9.49  tff(c_27874, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_27641])).
% 20.06/9.49  tff(c_28048, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27902, c_27874])).
% 20.06/9.49  tff(c_27889, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27875, c_14])).
% 20.06/9.49  tff(c_27905, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27889])).
% 20.06/9.49  tff(c_27883, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27875, c_12])).
% 20.06/9.49  tff(c_27899, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27883])).
% 20.06/9.49  tff(c_27907, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27899, c_6])).
% 20.06/9.49  tff(c_27910, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27875, c_27905, c_27907])).
% 20.06/9.49  tff(c_27968, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_27910, c_4])).
% 20.06/9.49  tff(c_31566, plain, (![A_810]: (k1_pre_topc(A_810, '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_810) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_810))) | ~l1_pre_topc(A_810))), inference(demodulation, [status(thm), theory('equality')], [c_27905, c_27910, c_27968])).
% 20.06/9.49  tff(c_31578, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_27327, c_31566])).
% 20.06/9.49  tff(c_31588, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23985, c_28048, c_31578])).
% 20.06/9.49  tff(c_31611, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_31588])).
% 20.06/9.49  tff(c_27335, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_27327, c_12])).
% 20.06/9.49  tff(c_27353, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23985, c_27335])).
% 20.06/9.49  tff(c_27421, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27353, c_28])).
% 20.06/9.49  tff(c_27430, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27421])).
% 20.06/9.49  tff(c_28052, plain, (m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28048, c_27430])).
% 20.06/9.49  tff(c_27341, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_27327, c_14])).
% 20.06/9.49  tff(c_27359, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_23985, c_27341])).
% 20.06/9.49  tff(c_28055, plain, (v1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28048, c_27359])).
% 20.06/9.49  tff(c_27525, plain, (![A_709, B_710]: (k2_struct_0(k1_pre_topc(A_709, B_710))=B_710 | ~m1_pre_topc(k1_pre_topc(A_709, B_710), A_709) | ~v1_pre_topc(k1_pre_topc(A_709, B_710)) | ~m1_subset_1(B_710, k1_zfmisc_1(u1_struct_0(A_709))) | ~l1_pre_topc(A_709))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.06/9.49  tff(c_27529, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_27353, c_27525])).
% 20.06/9.49  tff(c_27537, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_23985, c_27327, c_27359, c_27529])).
% 20.06/9.49  tff(c_28050, plain, (k2_struct_0(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28048, c_27537])).
% 20.06/9.49  tff(c_28072, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))))=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))) | ~m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), A_2) | ~v1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_28050, c_4])).
% 20.06/9.49  tff(c_35412, plain, (![A_879]: (k1_pre_topc(A_879, '#skF_2')=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))) | ~m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), A_879) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_879))) | ~l1_pre_topc(A_879))), inference(demodulation, [status(thm), theory('equality')], [c_28055, c_28050, c_28072])).
% 20.06/9.49  tff(c_35418, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28052, c_35412])).
% 20.06/9.49  tff(c_35424, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_27875, c_35418])).
% 20.06/9.49  tff(c_28053, plain, (m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28048, c_27353])).
% 20.06/9.49  tff(c_35426, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_35424, c_28053])).
% 20.06/9.49  tff(c_35435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31611, c_35426])).
% 20.06/9.49  tff(c_35436, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_31588])).
% 20.06/9.49  tff(c_23947, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_23462])).
% 20.06/9.49  tff(c_27330, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_27327, c_34])).
% 20.06/9.49  tff(c_27347, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23985, c_23947, c_27330])).
% 20.06/9.49  tff(c_27440, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_27347])).
% 20.06/9.49  tff(c_27466, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_27440])).
% 20.06/9.49  tff(c_27472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_27466])).
% 20.06/9.49  tff(c_27473, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_27347])).
% 20.06/9.49  tff(c_27503, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_27473])).
% 20.06/9.49  tff(c_28051, plain, (v1_compts_1(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28048, c_27503])).
% 20.06/9.49  tff(c_35442, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35436, c_28051])).
% 20.06/9.49  tff(c_35450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27964, c_35442])).
% 20.06/9.49  tff(c_35452, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_27896])).
% 20.06/9.49  tff(c_35451, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_27896])).
% 20.06/9.49  tff(c_35616, plain, (![A_880]: (v2_compts_1('#skF_2', A_880) | ~v1_compts_1(k1_pre_topc(A_880, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_880))) | ~l1_pre_topc(A_880))), inference(demodulation, [status(thm), theory('equality')], [c_35451, c_35451, c_35451, c_36])).
% 20.06/9.49  tff(c_35628, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27875, c_35616])).
% 20.06/9.49  tff(c_35637, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_35452, c_35628])).
% 20.06/9.49  tff(c_35639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23993, c_35637])).
% 20.06/9.49  tff(c_35641, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_27473])).
% 20.06/9.49  tff(c_35640, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_27473])).
% 20.06/9.49  tff(c_35717, plain, (![A_883]: (v1_compts_1(k1_pre_topc(A_883, '#skF_2')) | ~v2_compts_1('#skF_2', A_883) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_883))) | ~l1_pre_topc(A_883))), inference(demodulation, [status(thm), theory('equality')], [c_35640, c_35640, c_35640, c_38])).
% 20.06/9.49  tff(c_35723, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_27327, c_35717])).
% 20.06/9.49  tff(c_35732, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_23985, c_23947, c_35723])).
% 20.06/9.49  tff(c_35734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35641, c_35732])).
% 20.06/9.49  tff(c_35735, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_23992])).
% 20.06/9.49  tff(c_36181, plain, (![A_908, B_909]: (u1_struct_0(g1_pre_topc(A_908, B_909))=A_908 | ~m1_subset_1(B_909, k1_zfmisc_1(k1_zfmisc_1(A_908))) | ~v1_pre_topc(g1_pre_topc(A_908, B_909)) | ~l1_pre_topc(g1_pre_topc(A_908, B_909)))), inference(reflexivity, [status(thm), theory('equality')], [c_172])).
% 20.06/9.49  tff(c_36405, plain, (![A_915]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_915), u1_pre_topc(A_915)))=u1_struct_0(A_915) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_915), u1_pre_topc(A_915))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_915), u1_pre_topc(A_915))) | ~l1_pre_topc(A_915))), inference(resolution, [status(thm)], [c_16, c_36181])).
% 20.06/9.49  tff(c_36429, plain, (![A_916]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_916), u1_pre_topc(A_916)))=u1_struct_0(A_916) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_916), u1_pre_topc(A_916))) | ~l1_pre_topc(A_916))), inference(resolution, [status(thm)], [c_68, c_36405])).
% 20.06/9.49  tff(c_36441, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_23985, c_36429])).
% 20.06/9.49  tff(c_36455, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36441])).
% 20.06/9.49  tff(c_35799, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_23463, c_23948, c_48])).
% 20.06/9.49  tff(c_36459, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36455, c_35799])).
% 20.06/9.49  tff(c_36462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35735, c_36459])).
% 20.06/9.49  tff(c_36464, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 20.06/9.49  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_36478, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36464, c_52])).
% 20.06/9.49  tff(c_36479, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36478])).
% 20.06/9.49  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_36498, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_36464, c_54])).
% 20.06/9.49  tff(c_36747, plain, (![A_958, C_959]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_958, C_959)), u1_pre_topc(k1_pre_topc(A_958, C_959)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_958), u1_pre_topc(A_958)), C_959) | ~m1_subset_1(C_959, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_958), u1_pre_topc(A_958))))) | ~m1_subset_1(C_959, k1_zfmisc_1(u1_struct_0(A_958))) | ~l1_pre_topc(A_958))), inference(cnfTransformation, [status(thm)], [f_106])).
% 20.06/9.49  tff(c_36751, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36498, c_36747])).
% 20.06/9.49  tff(c_36757, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36751])).
% 20.06/9.49  tff(c_36883, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_36757])).
% 20.06/9.49  tff(c_36512, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_36498, c_14])).
% 20.06/9.49  tff(c_36517, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_36512])).
% 20.06/9.49  tff(c_36523, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_36517])).
% 20.06/9.49  tff(c_36529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36523])).
% 20.06/9.49  tff(c_36531, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_36512])).
% 20.06/9.49  tff(c_36484, plain, (![D_923, B_924, C_925, A_926]: (D_923=B_924 | g1_pre_topc(C_925, D_923)!=g1_pre_topc(A_926, B_924) | ~m1_subset_1(B_924, k1_zfmisc_1(k1_zfmisc_1(A_926))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_36486, plain, (![A_1, B_924, A_926]: (u1_pre_topc(A_1)=B_924 | g1_pre_topc(A_926, B_924)!=A_1 | ~m1_subset_1(B_924, k1_zfmisc_1(k1_zfmisc_1(A_926))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_36484])).
% 20.06/9.49  tff(c_36680, plain, (![A_955, B_956]: (u1_pre_topc(g1_pre_topc(A_955, B_956))=B_956 | ~m1_subset_1(B_956, k1_zfmisc_1(k1_zfmisc_1(A_955))) | ~v1_pre_topc(g1_pre_topc(A_955, B_956)) | ~l1_pre_topc(g1_pre_topc(A_955, B_956)))), inference(reflexivity, [status(thm), theory('equality')], [c_36486])).
% 20.06/9.49  tff(c_36735, plain, (![A_957]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_957), u1_pre_topc(A_957)))=u1_pre_topc(A_957) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_957), u1_pre_topc(A_957))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_957), u1_pre_topc(A_957))) | ~l1_pre_topc(A_957))), inference(resolution, [status(thm)], [c_16, c_36680])).
% 20.06/9.49  tff(c_36758, plain, (![A_960]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_960), u1_pre_topc(A_960)))=u1_pre_topc(A_960) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_960), u1_pre_topc(A_960))) | ~l1_pre_topc(A_960))), inference(resolution, [status(thm)], [c_68, c_36735])).
% 20.06/9.49  tff(c_36764, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36531, c_36758])).
% 20.06/9.49  tff(c_36774, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36764])).
% 20.06/9.49  tff(c_36799, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_36774, c_16])).
% 20.06/9.49  tff(c_36820, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36799])).
% 20.06/9.49  tff(c_36493, plain, (![C_927, A_928, D_929, B_930]: (C_927=A_928 | g1_pre_topc(C_927, D_929)!=g1_pre_topc(A_928, B_930) | ~m1_subset_1(B_930, k1_zfmisc_1(k1_zfmisc_1(A_928))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_36497, plain, (![A_1, C_927, D_929]: (u1_struct_0(A_1)=C_927 | g1_pre_topc(C_927, D_929)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_36493])).
% 20.06/9.49  tff(c_37370, plain, (![C_971, D_972]: (u1_struct_0(g1_pre_topc(C_971, D_972))=C_971 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_971, D_972)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_971, D_972))))) | ~v1_pre_topc(g1_pre_topc(C_971, D_972)) | ~l1_pre_topc(g1_pre_topc(C_971, D_972)))), inference(reflexivity, [status(thm), theory('equality')], [c_36497])).
% 20.06/9.49  tff(c_37388, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_36774, c_37370])).
% 20.06/9.49  tff(c_37403, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36820, c_37388])).
% 20.06/9.49  tff(c_37426, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_37403])).
% 20.06/9.49  tff(c_37432, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_37426])).
% 20.06/9.49  tff(c_37438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_37432])).
% 20.06/9.49  tff(c_37439, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_37403])).
% 20.06/9.49  tff(c_37466, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_37439, c_36498])).
% 20.06/9.49  tff(c_37472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36883, c_37466])).
% 20.06/9.49  tff(c_37474, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_36757])).
% 20.06/9.49  tff(c_37480, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37474, c_32])).
% 20.06/9.49  tff(c_37494, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_37480])).
% 20.06/9.49  tff(c_37495, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36479, c_37494])).
% 20.06/9.49  tff(c_37593, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_37495])).
% 20.06/9.49  tff(c_37483, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37474, c_26])).
% 20.06/9.49  tff(c_37498, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37483])).
% 20.06/9.49  tff(c_37473, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_36757])).
% 20.06/9.49  tff(c_37558, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_37498, c_37473])).
% 20.06/9.49  tff(c_38021, plain, (![C_981, D_982]: (u1_struct_0(g1_pre_topc(C_981, D_982))=C_981 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_981, D_982)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_981, D_982))))) | ~v1_pre_topc(g1_pre_topc(C_981, D_982)) | ~l1_pre_topc(g1_pre_topc(C_981, D_982)))), inference(reflexivity, [status(thm), theory('equality')], [c_36497])).
% 20.06/9.49  tff(c_38042, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_36774, c_38021])).
% 20.06/9.49  tff(c_38059, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36820, c_38042])).
% 20.06/9.49  tff(c_38083, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_38059])).
% 20.06/9.49  tff(c_38089, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_38083])).
% 20.06/9.49  tff(c_38095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38089])).
% 20.06/9.49  tff(c_38096, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_38059])).
% 20.06/9.49  tff(c_37488, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37474, c_14])).
% 20.06/9.49  tff(c_37504, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37488])).
% 20.06/9.49  tff(c_37485, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37474, c_12])).
% 20.06/9.49  tff(c_37501, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37485])).
% 20.06/9.49  tff(c_37580, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37501, c_6])).
% 20.06/9.49  tff(c_37583, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37474, c_37504, c_37580])).
% 20.06/9.49  tff(c_37587, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_37583, c_4])).
% 20.06/9.49  tff(c_38462, plain, (![A_989]: (k1_pre_topc(A_989, '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_989) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_989))) | ~l1_pre_topc(A_989))), inference(demodulation, [status(thm), theory('equality')], [c_37504, c_37583, c_37587])).
% 20.06/9.49  tff(c_38471, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_38096, c_38462])).
% 20.06/9.49  tff(c_38482, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_37474, c_37558, c_38471])).
% 20.06/9.49  tff(c_38807, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_38482])).
% 20.06/9.49  tff(c_36511, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_36498, c_12])).
% 20.06/9.49  tff(c_36686, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36511])).
% 20.06/9.49  tff(c_36691, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36686, c_28])).
% 20.06/9.49  tff(c_36703, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36691])).
% 20.06/9.49  tff(c_37560, plain, (m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37558, c_36703])).
% 20.06/9.49  tff(c_36530, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_36512])).
% 20.06/9.49  tff(c_37565, plain, (v1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_37558, c_36530])).
% 20.06/9.49  tff(c_36688, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_36686, c_6])).
% 20.06/9.49  tff(c_36700, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36498, c_36530, c_36688])).
% 20.06/9.49  tff(c_37561, plain, (k2_struct_0(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_37558, c_36700])).
% 20.06/9.49  tff(c_37597, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))))=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))) | ~m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), A_2) | ~v1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_37561, c_4])).
% 20.06/9.49  tff(c_40292, plain, (![A_1041]: (k1_pre_topc(A_1041, '#skF_2')=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))) | ~m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), A_1041) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1041))) | ~l1_pre_topc(A_1041))), inference(demodulation, [status(thm), theory('equality')], [c_37565, c_37561, c_37597])).
% 20.06/9.49  tff(c_40298, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37560, c_40292])).
% 20.06/9.49  tff(c_40304, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37474, c_40298])).
% 20.06/9.49  tff(c_37562, plain, (m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_37558, c_36686])).
% 20.06/9.49  tff(c_40367, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40304, c_37562])).
% 20.06/9.49  tff(c_40376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38807, c_40367])).
% 20.06/9.49  tff(c_40377, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38482])).
% 20.06/9.49  tff(c_36463, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 20.06/9.49  tff(c_36620, plain, (![A_943, B_944]: (v1_compts_1(k1_pre_topc(A_943, B_944)) | ~v2_compts_1(B_944, A_943) | k1_xboole_0=B_944 | ~v2_pre_topc(A_943) | ~m1_subset_1(B_944, k1_zfmisc_1(u1_struct_0(A_943))) | ~l1_pre_topc(A_943))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.06/9.49  tff(c_36626, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_36498, c_36620])).
% 20.06/9.49  tff(c_36629, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36463, c_36626])).
% 20.06/9.49  tff(c_36630, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_36629])).
% 20.06/9.49  tff(c_36636, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_36630])).
% 20.06/9.49  tff(c_36642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36636])).
% 20.06/9.49  tff(c_36643, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_36629])).
% 20.06/9.49  tff(c_36651, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_36643])).
% 20.06/9.49  tff(c_37563, plain, (v1_compts_1(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_37558, c_36651])).
% 20.06/9.49  tff(c_40384, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40377, c_37563])).
% 20.06/9.49  tff(c_40391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37593, c_40384])).
% 20.06/9.49  tff(c_40393, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_37495])).
% 20.06/9.49  tff(c_40392, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_37495])).
% 20.06/9.49  tff(c_40639, plain, (![A_1049]: (v2_compts_1('#skF_2', A_1049) | ~v1_compts_1(k1_pre_topc(A_1049, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1049))) | ~l1_pre_topc(A_1049))), inference(demodulation, [status(thm), theory('equality')], [c_40392, c_40392, c_40392, c_36])).
% 20.06/9.49  tff(c_40648, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37474, c_40639])).
% 20.06/9.49  tff(c_40654, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40393, c_40648])).
% 20.06/9.49  tff(c_40656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36479, c_40654])).
% 20.06/9.49  tff(c_40658, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_36643])).
% 20.06/9.49  tff(c_40657, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36643])).
% 20.06/9.49  tff(c_40672, plain, (![A_1050]: (v1_compts_1(k1_pre_topc(A_1050, '#skF_2')) | ~v2_compts_1('#skF_2', A_1050) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1050))) | ~l1_pre_topc(A_1050))), inference(demodulation, [status(thm), theory('equality')], [c_40657, c_40657, c_40657, c_38])).
% 20.06/9.49  tff(c_40678, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_36498, c_40672])).
% 20.06/9.49  tff(c_40681, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36463, c_40678])).
% 20.06/9.49  tff(c_40683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40658, c_40681])).
% 20.06/9.49  tff(c_40684, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_36478])).
% 20.06/9.49  tff(c_40704, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_36464, c_54])).
% 20.06/9.49  tff(c_40718, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_40704, c_14])).
% 20.06/9.49  tff(c_40725, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_40718])).
% 20.06/9.49  tff(c_40731, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_40725])).
% 20.06/9.49  tff(c_40737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_40731])).
% 20.06/9.49  tff(c_40739, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_40718])).
% 20.06/9.49  tff(c_40690, plain, (![D_1051, B_1052, C_1053, A_1054]: (D_1051=B_1052 | g1_pre_topc(C_1053, D_1051)!=g1_pre_topc(A_1054, B_1052) | ~m1_subset_1(B_1052, k1_zfmisc_1(k1_zfmisc_1(A_1054))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_40692, plain, (![A_1, B_1052, A_1054]: (u1_pre_topc(A_1)=B_1052 | g1_pre_topc(A_1054, B_1052)!=A_1 | ~m1_subset_1(B_1052, k1_zfmisc_1(k1_zfmisc_1(A_1054))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_40690])).
% 20.06/9.49  tff(c_40890, plain, (![A_1083, B_1084]: (u1_pre_topc(g1_pre_topc(A_1083, B_1084))=B_1084 | ~m1_subset_1(B_1084, k1_zfmisc_1(k1_zfmisc_1(A_1083))) | ~v1_pre_topc(g1_pre_topc(A_1083, B_1084)) | ~l1_pre_topc(g1_pre_topc(A_1083, B_1084)))), inference(reflexivity, [status(thm), theory('equality')], [c_40692])).
% 20.06/9.49  tff(c_40955, plain, (![A_1087]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1087), u1_pre_topc(A_1087)))=u1_pre_topc(A_1087) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1087), u1_pre_topc(A_1087))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1087), u1_pre_topc(A_1087))) | ~l1_pre_topc(A_1087))), inference(resolution, [status(thm)], [c_16, c_40890])).
% 20.06/9.49  tff(c_41020, plain, (![A_1090]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1090), u1_pre_topc(A_1090)))=u1_pre_topc(A_1090) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1090), u1_pre_topc(A_1090))) | ~l1_pre_topc(A_1090))), inference(resolution, [status(thm)], [c_68, c_40955])).
% 20.06/9.49  tff(c_41029, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40739, c_41020])).
% 20.06/9.49  tff(c_41039, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_41029])).
% 20.06/9.49  tff(c_41064, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41039, c_16])).
% 20.06/9.49  tff(c_41085, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_40739, c_41064])).
% 20.06/9.49  tff(c_40699, plain, (![C_1055, A_1056, D_1057, B_1058]: (C_1055=A_1056 | g1_pre_topc(C_1055, D_1057)!=g1_pre_topc(A_1056, B_1058) | ~m1_subset_1(B_1058, k1_zfmisc_1(k1_zfmisc_1(A_1056))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_40703, plain, (![A_1, C_1055, D_1057]: (u1_struct_0(A_1)=C_1055 | g1_pre_topc(C_1055, D_1057)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_40699])).
% 20.06/9.49  tff(c_41424, plain, (![C_1096, D_1097]: (u1_struct_0(g1_pre_topc(C_1096, D_1097))=C_1096 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_1096, D_1097)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1096, D_1097))))) | ~v1_pre_topc(g1_pre_topc(C_1096, D_1097)) | ~l1_pre_topc(g1_pre_topc(C_1096, D_1097)))), inference(reflexivity, [status(thm), theory('equality')], [c_40703])).
% 20.06/9.49  tff(c_41436, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41039, c_41424])).
% 20.06/9.49  tff(c_41457, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40739, c_41085, c_41436])).
% 20.06/9.49  tff(c_41476, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_41457])).
% 20.06/9.49  tff(c_41482, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_41476])).
% 20.06/9.49  tff(c_41488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_41482])).
% 20.06/9.49  tff(c_41489, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_41457])).
% 20.06/9.49  tff(c_41515, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41489, c_40704])).
% 20.06/9.49  tff(c_41521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40684, c_41515])).
% 20.06/9.49  tff(c_41523, plain, (~v2_compts_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 20.06/9.49  tff(c_58, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_41548, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41523, c_58])).
% 20.06/9.49  tff(c_41549, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_41548])).
% 20.06/9.49  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.06/9.49  tff(c_41558, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_41523, c_60])).
% 20.06/9.49  tff(c_42032, plain, (![A_1146, C_1147]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_1146, C_1147)), u1_pre_topc(k1_pre_topc(A_1146, C_1147)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_1146), u1_pre_topc(A_1146)), C_1147) | ~m1_subset_1(C_1147, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1146), u1_pre_topc(A_1146))))) | ~m1_subset_1(C_1147, k1_zfmisc_1(u1_struct_0(A_1146))) | ~l1_pre_topc(A_1146))), inference(cnfTransformation, [status(thm)], [f_106])).
% 20.06/9.49  tff(c_42042, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_41558, c_42032])).
% 20.06/9.49  tff(c_42052, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42042])).
% 20.06/9.49  tff(c_42068, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_42052])).
% 20.06/9.49  tff(c_41572, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_41558, c_14])).
% 20.06/9.49  tff(c_41596, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_41572])).
% 20.06/9.49  tff(c_41602, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_41596])).
% 20.06/9.49  tff(c_41608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_41602])).
% 20.06/9.49  tff(c_41610, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_41572])).
% 20.06/9.49  tff(c_41579, plain, (![D_1109, B_1110, C_1111, A_1112]: (D_1109=B_1110 | g1_pre_topc(C_1111, D_1109)!=g1_pre_topc(A_1112, B_1110) | ~m1_subset_1(B_1110, k1_zfmisc_1(k1_zfmisc_1(A_1112))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_41581, plain, (![A_1, B_1110, A_1112]: (u1_pre_topc(A_1)=B_1110 | g1_pre_topc(A_1112, B_1110)!=A_1 | ~m1_subset_1(B_1110, k1_zfmisc_1(k1_zfmisc_1(A_1112))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_41579])).
% 20.06/9.49  tff(c_41754, plain, (![A_1137, B_1138]: (u1_pre_topc(g1_pre_topc(A_1137, B_1138))=B_1138 | ~m1_subset_1(B_1138, k1_zfmisc_1(k1_zfmisc_1(A_1137))) | ~v1_pre_topc(g1_pre_topc(A_1137, B_1138)) | ~l1_pre_topc(g1_pre_topc(A_1137, B_1138)))), inference(reflexivity, [status(thm), theory('equality')], [c_41581])).
% 20.06/9.49  tff(c_41813, plain, (![A_1143]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1143), u1_pre_topc(A_1143)))=u1_pre_topc(A_1143) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1143), u1_pre_topc(A_1143))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1143), u1_pre_topc(A_1143))) | ~l1_pre_topc(A_1143))), inference(resolution, [status(thm)], [c_16, c_41754])).
% 20.06/9.49  tff(c_41825, plain, (![A_1144]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1144), u1_pre_topc(A_1144)))=u1_pre_topc(A_1144) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1144), u1_pre_topc(A_1144))) | ~l1_pre_topc(A_1144))), inference(resolution, [status(thm)], [c_68, c_41813])).
% 20.06/9.49  tff(c_41831, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_41610, c_41825])).
% 20.06/9.49  tff(c_41841, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_41831])).
% 20.06/9.49  tff(c_41853, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41841, c_2])).
% 20.06/9.49  tff(c_41876, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_41853])).
% 20.06/9.49  tff(c_42503, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_41876])).
% 20.06/9.49  tff(c_42509, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_42503])).
% 20.06/9.49  tff(c_42515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_42509])).
% 20.06/9.49  tff(c_42517, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_41876])).
% 20.06/9.49  tff(c_41865, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41841, c_16])).
% 20.06/9.49  tff(c_41884, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_41865])).
% 20.06/9.49  tff(c_41588, plain, (![C_1113, A_1114, D_1115, B_1116]: (C_1113=A_1114 | g1_pre_topc(C_1113, D_1115)!=g1_pre_topc(A_1114, B_1116) | ~m1_subset_1(B_1116, k1_zfmisc_1(k1_zfmisc_1(A_1114))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_41592, plain, (![A_1, C_1113, D_1115]: (u1_struct_0(A_1)=C_1113 | g1_pre_topc(C_1113, D_1115)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_41588])).
% 20.06/9.49  tff(c_42620, plain, (![C_1161, D_1162]: (u1_struct_0(g1_pre_topc(C_1161, D_1162))=C_1161 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_1161, D_1162)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1161, D_1162))))) | ~v1_pre_topc(g1_pre_topc(C_1161, D_1162)) | ~l1_pre_topc(g1_pre_topc(C_1161, D_1162)))), inference(reflexivity, [status(thm), theory('equality')], [c_41592])).
% 20.06/9.49  tff(c_42638, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41841, c_42620])).
% 20.06/9.49  tff(c_42653, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_42517, c_41884, c_42638])).
% 20.06/9.49  tff(c_42657, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42653, c_41558])).
% 20.06/9.49  tff(c_42659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42068, c_42657])).
% 20.06/9.49  tff(c_42661, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_42052])).
% 20.06/9.49  tff(c_42664, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42661, c_32])).
% 20.06/9.49  tff(c_42678, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_42664])).
% 20.06/9.49  tff(c_42679, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_41549, c_42678])).
% 20.06/9.49  tff(c_42692, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_42679])).
% 20.06/9.49  tff(c_42670, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42661, c_26])).
% 20.06/9.49  tff(c_42685, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42670])).
% 20.06/9.49  tff(c_42660, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_42052])).
% 20.06/9.49  tff(c_42761, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42685, c_42660])).
% 20.06/9.49  tff(c_42947, plain, (![C_1165, D_1166]: (u1_struct_0(g1_pre_topc(C_1165, D_1166))=C_1165 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_1165, D_1166)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1165, D_1166))))) | ~v1_pre_topc(g1_pre_topc(C_1165, D_1166)) | ~l1_pre_topc(g1_pre_topc(C_1165, D_1166)))), inference(reflexivity, [status(thm), theory('equality')], [c_41592])).
% 20.06/9.49  tff(c_42965, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41841, c_42947])).
% 20.06/9.49  tff(c_42980, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_41884, c_42965])).
% 20.06/9.49  tff(c_43010, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_42980])).
% 20.06/9.49  tff(c_43016, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_43010])).
% 20.06/9.49  tff(c_43022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_43016])).
% 20.06/9.49  tff(c_43023, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_42980])).
% 20.06/9.49  tff(c_42675, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42661, c_14])).
% 20.06/9.49  tff(c_42691, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42675])).
% 20.06/9.49  tff(c_42672, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42661, c_12])).
% 20.06/9.49  tff(c_42688, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42672])).
% 20.06/9.49  tff(c_42747, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42688, c_6])).
% 20.06/9.49  tff(c_42750, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42661, c_42691, c_42747])).
% 20.06/9.49  tff(c_42754, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_42750, c_4])).
% 20.06/9.49  tff(c_43458, plain, (![A_1177]: (k1_pre_topc(A_1177, '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_1177) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1177))) | ~l1_pre_topc(A_1177))), inference(demodulation, [status(thm), theory('equality')], [c_42691, c_42750, c_42754])).
% 20.06/9.49  tff(c_43467, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_43023, c_43458])).
% 20.06/9.49  tff(c_43478, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_42661, c_42761, c_43467])).
% 20.06/9.49  tff(c_43803, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_43478])).
% 20.06/9.49  tff(c_41571, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_41558, c_12])).
% 20.06/9.49  tff(c_41765, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_41571])).
% 20.06/9.49  tff(c_41768, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_41765, c_28])).
% 20.06/9.49  tff(c_41777, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_41768])).
% 20.06/9.49  tff(c_42764, plain, (m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42761, c_41777])).
% 20.06/9.49  tff(c_41609, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_41572])).
% 20.06/9.49  tff(c_42768, plain, (v1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42761, c_41609])).
% 20.06/9.49  tff(c_41787, plain, (![A_1141, B_1142]: (k2_struct_0(k1_pre_topc(A_1141, B_1142))=B_1142 | ~m1_pre_topc(k1_pre_topc(A_1141, B_1142), A_1141) | ~v1_pre_topc(k1_pre_topc(A_1141, B_1142)) | ~m1_subset_1(B_1142, k1_zfmisc_1(u1_struct_0(A_1141))) | ~l1_pre_topc(A_1141))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.06/9.49  tff(c_41789, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_41765, c_41787])).
% 20.06/9.49  tff(c_41792, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_41558, c_41609, c_41789])).
% 20.06/9.49  tff(c_42763, plain, (k2_struct_0(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42761, c_41792])).
% 20.06/9.49  tff(c_42838, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))))=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))) | ~m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), A_2) | ~v1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_42763, c_4])).
% 20.06/9.49  tff(c_45286, plain, (![A_1229]: (k1_pre_topc(A_1229, '#skF_2')=g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))) | ~m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), A_1229) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1229))) | ~l1_pre_topc(A_1229))), inference(demodulation, [status(thm), theory('equality')], [c_42768, c_42763, c_42838])).
% 20.06/9.49  tff(c_45292, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42764, c_45286])).
% 20.06/9.49  tff(c_45298, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42661, c_45292])).
% 20.06/9.49  tff(c_42765, plain, (m1_pre_topc(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42761, c_41765])).
% 20.06/9.49  tff(c_45306, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_45298, c_42765])).
% 20.06/9.49  tff(c_45315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43803, c_45306])).
% 20.06/9.49  tff(c_45316, plain, (g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_43478])).
% 20.06/9.49  tff(c_41522, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 20.06/9.49  tff(c_41616, plain, (![A_1119, B_1120]: (v1_compts_1(k1_pre_topc(A_1119, B_1120)) | ~v2_compts_1(B_1120, A_1119) | k1_xboole_0=B_1120 | ~v2_pre_topc(A_1119) | ~m1_subset_1(B_1120, k1_zfmisc_1(u1_struct_0(A_1119))) | ~l1_pre_topc(A_1119))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.06/9.49  tff(c_41619, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_41558, c_41616])).
% 20.06/9.49  tff(c_41622, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_41522, c_41619])).
% 20.06/9.49  tff(c_41676, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_41622])).
% 20.06/9.49  tff(c_41683, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_41676])).
% 20.06/9.49  tff(c_41689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_41683])).
% 20.06/9.49  tff(c_41690, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_41622])).
% 20.06/9.49  tff(c_41697, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_41690])).
% 20.06/9.49  tff(c_42766, plain, (v1_compts_1(g1_pre_topc('#skF_2', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42761, c_41697])).
% 20.06/9.49  tff(c_45321, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_45316, c_42766])).
% 20.06/9.49  tff(c_45329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42692, c_45321])).
% 20.06/9.49  tff(c_45331, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_42679])).
% 20.06/9.49  tff(c_45330, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42679])).
% 20.06/9.49  tff(c_45612, plain, (![A_1233]: (v2_compts_1('#skF_2', A_1233) | ~v1_compts_1(k1_pre_topc(A_1233, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1233))) | ~l1_pre_topc(A_1233))), inference(demodulation, [status(thm), theory('equality')], [c_45330, c_45330, c_45330, c_36])).
% 20.06/9.49  tff(c_45621, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42661, c_45612])).
% 20.06/9.49  tff(c_45627, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_45331, c_45621])).
% 20.06/9.49  tff(c_45629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41549, c_45627])).
% 20.06/9.49  tff(c_45631, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_41690])).
% 20.06/9.49  tff(c_45630, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_41690])).
% 20.06/9.49  tff(c_45644, plain, (![A_1234]: (v1_compts_1(k1_pre_topc(A_1234, '#skF_2')) | ~v2_compts_1('#skF_2', A_1234) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1234))) | ~l1_pre_topc(A_1234))), inference(demodulation, [status(thm), theory('equality')], [c_45630, c_45630, c_45630, c_38])).
% 20.06/9.49  tff(c_45650, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_41558, c_45644])).
% 20.06/9.49  tff(c_45653, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_41610, c_41522, c_45650])).
% 20.06/9.49  tff(c_45655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45631, c_45653])).
% 20.06/9.49  tff(c_45656, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_41548])).
% 20.06/9.49  tff(c_45661, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_41523, c_60])).
% 20.06/9.49  tff(c_45671, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_45661, c_14])).
% 20.06/9.49  tff(c_45707, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_45671])).
% 20.06/9.49  tff(c_45713, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_45707])).
% 20.06/9.49  tff(c_45719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_45713])).
% 20.06/9.49  tff(c_45721, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_45671])).
% 20.06/9.49  tff(c_45700, plain, (![D_1247, B_1248, C_1249, A_1250]: (D_1247=B_1248 | g1_pre_topc(C_1249, D_1247)!=g1_pre_topc(A_1250, B_1248) | ~m1_subset_1(B_1248, k1_zfmisc_1(k1_zfmisc_1(A_1250))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_45702, plain, (![A_1, B_1248, A_1250]: (u1_pre_topc(A_1)=B_1248 | g1_pre_topc(A_1250, B_1248)!=A_1 | ~m1_subset_1(B_1248, k1_zfmisc_1(k1_zfmisc_1(A_1250))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_45700])).
% 20.06/9.49  tff(c_45866, plain, (![A_1271, B_1272]: (u1_pre_topc(g1_pre_topc(A_1271, B_1272))=B_1272 | ~m1_subset_1(B_1272, k1_zfmisc_1(k1_zfmisc_1(A_1271))) | ~v1_pre_topc(g1_pre_topc(A_1271, B_1272)) | ~l1_pre_topc(g1_pre_topc(A_1271, B_1272)))), inference(reflexivity, [status(thm), theory('equality')], [c_45702])).
% 20.06/9.49  tff(c_45926, plain, (![A_1277]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1277), u1_pre_topc(A_1277)))=u1_pre_topc(A_1277) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1277), u1_pre_topc(A_1277))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1277), u1_pre_topc(A_1277))) | ~l1_pre_topc(A_1277))), inference(resolution, [status(thm)], [c_16, c_45866])).
% 20.06/9.49  tff(c_45949, plain, (![A_1280]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1280), u1_pre_topc(A_1280)))=u1_pre_topc(A_1280) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1280), u1_pre_topc(A_1280))) | ~l1_pre_topc(A_1280))), inference(resolution, [status(thm)], [c_68, c_45926])).
% 20.06/9.49  tff(c_45955, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_45721, c_45949])).
% 20.06/9.49  tff(c_45965, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_45955])).
% 20.06/9.49  tff(c_45990, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_45965, c_16])).
% 20.06/9.49  tff(c_46011, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_45721, c_45990])).
% 20.06/9.49  tff(c_45690, plain, (![C_1243, A_1244, D_1245, B_1246]: (C_1243=A_1244 | g1_pre_topc(C_1243, D_1245)!=g1_pre_topc(A_1244, B_1246) | ~m1_subset_1(B_1246, k1_zfmisc_1(k1_zfmisc_1(A_1244))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.06/9.49  tff(c_45694, plain, (![A_1, C_1243, D_1245]: (u1_struct_0(A_1)=C_1243 | g1_pre_topc(C_1243, D_1245)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_45690])).
% 20.06/9.49  tff(c_46405, plain, (![C_1284, D_1285]: (u1_struct_0(g1_pre_topc(C_1284, D_1285))=C_1284 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_1284, D_1285)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1284, D_1285))))) | ~v1_pre_topc(g1_pre_topc(C_1284, D_1285)) | ~l1_pre_topc(g1_pre_topc(C_1284, D_1285)))), inference(reflexivity, [status(thm), theory('equality')], [c_45694])).
% 20.06/9.49  tff(c_46423, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_45965, c_46405])).
% 20.06/9.49  tff(c_46438, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_45721, c_46011, c_46423])).
% 20.06/9.49  tff(c_46457, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_46438])).
% 20.06/9.49  tff(c_46463, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_46457])).
% 20.06/9.49  tff(c_46469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_46463])).
% 20.06/9.49  tff(c_46470, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_46438])).
% 20.06/9.49  tff(c_46490, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46470, c_45661])).
% 20.06/9.49  tff(c_46496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45656, c_46490])).
% 20.06/9.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.06/9.49  
% 20.06/9.49  Inference rules
% 20.06/9.49  ----------------------
% 20.06/9.49  #Ref     : 66
% 20.06/9.49  #Sup     : 12570
% 20.06/9.49  #Fact    : 0
% 20.06/9.49  #Define  : 0
% 20.06/9.49  #Split   : 110
% 20.06/9.49  #Chain   : 0
% 20.06/9.49  #Close   : 0
% 20.06/9.49  
% 20.06/9.49  Ordering : KBO
% 20.06/9.49  
% 20.06/9.49  Simplification rules
% 20.06/9.49  ----------------------
% 20.06/9.49  #Subsume      : 3558
% 20.06/9.49  #Demod        : 14406
% 20.06/9.49  #Tautology    : 1859
% 20.06/9.49  #SimpNegUnit  : 152
% 20.06/9.49  #BackRed      : 355
% 20.06/9.49  
% 20.06/9.49  #Partial instantiations: 0
% 20.06/9.49  #Strategies tried      : 1
% 20.06/9.49  
% 20.06/9.49  Timing (in seconds)
% 20.06/9.49  ----------------------
% 20.06/9.50  Preprocessing        : 0.47
% 20.06/9.50  Parsing              : 0.24
% 20.06/9.50  CNF conversion       : 0.04
% 20.06/9.50  Main loop            : 7.98
% 20.06/9.50  Inferencing          : 1.79
% 20.06/9.50  Reduction            : 2.87
% 20.06/9.50  Demodulation         : 2.20
% 20.06/9.50  BG Simplification    : 0.30
% 20.06/9.50  Subsumption          : 2.63
% 20.06/9.50  Abstraction          : 0.45
% 20.06/9.50  MUC search           : 0.00
% 20.06/9.50  Cooper               : 0.00
% 20.06/9.50  Total                : 8.62
% 20.06/9.50  Index Insertion      : 0.00
% 20.06/9.50  Index Deletion       : 0.00
% 20.06/9.50  Index Matching       : 0.00
% 20.06/9.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
