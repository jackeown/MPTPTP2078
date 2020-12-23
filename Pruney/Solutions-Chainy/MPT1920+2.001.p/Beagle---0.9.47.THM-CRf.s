%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:45 EST 2020

% Result     : Theorem 11.05s
% Output     : CNFRefutation 11.05s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 604 expanded)
%              Number of leaves         :   34 ( 236 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 (2006 expanded)
%              Number of equality atoms :   22 (  98 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_yellow_6 > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_waybel_0(B,A)
           => ! [C] :
                ( m1_yellow_6(C,A,B)
               => ! [D] :
                    ( m1_yellow_6(D,A,C)
                   => m1_yellow_6(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_6)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ! [C] :
              ( m1_yellow_0(C,B)
             => m1_yellow_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_6)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r1_tarski(A,B)
       => ( k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A)
          & k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_53,plain,(
    ! [C_58,A_59,B_60] :
      ( l1_waybel_0(C_58,A_59)
      | ~ m1_yellow_6(C_58,A_59,B_60)
      | ~ l1_waybel_0(B_60,A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_62,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_56])).

tff(c_36,plain,(
    m1_yellow_6('#skF_4','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_59,plain,
    ( l1_waybel_0('#skF_4','#skF_1')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_65,plain,
    ( l1_waybel_0('#skF_4','#skF_1')
    | ~ l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_59])).

tff(c_73,plain,(
    l1_waybel_0('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_65])).

tff(c_16,plain,(
    ! [B_16,A_14] :
      ( l1_orders_2(B_16)
      | ~ l1_waybel_0(B_16,A_14)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_16])).

tff(c_79,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_76])).

tff(c_132,plain,(
    ! [C_77,B_78,A_79] :
      ( m1_yellow_0(C_77,B_78)
      | ~ m1_yellow_6(C_77,A_79,B_78)
      | ~ l1_waybel_0(C_77,A_79)
      | ~ l1_waybel_0(B_78,A_79)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_138,plain,
    ( m1_yellow_0('#skF_4','#skF_3')
    | ~ l1_waybel_0('#skF_4','#skF_1')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_132])).

tff(c_144,plain,(
    m1_yellow_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62,c_73,c_138])).

tff(c_43,plain,(
    ! [B_48,A_49] :
      ( l1_orders_2(B_48)
      | ~ l1_waybel_0(B_48,A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_43])).

tff(c_49,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_135,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_141,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_62,c_135])).

tff(c_32,plain,(
    ! [C_36,A_30,B_34] :
      ( m1_yellow_0(C_36,A_30)
      | ~ m1_yellow_0(C_36,B_34)
      | ~ m1_yellow_0(B_34,A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_156,plain,(
    ! [A_85] :
      ( m1_yellow_0('#skF_4',A_85)
      | ~ m1_yellow_0('#skF_3',A_85)
      | ~ l1_orders_2(A_85) ) ),
    inference(resolution,[status(thm)],[c_144,c_32])).

tff(c_159,plain,
    ( m1_yellow_0('#skF_4','#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_141,c_156])).

tff(c_162,plain,(
    m1_yellow_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_159])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( v1_funct_1(u1_waybel_0(A_17,B_18))
      | ~ l1_waybel_0(B_18,A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [B_13,A_11] :
      ( r1_tarski(u1_struct_0(B_13),u1_struct_0(A_11))
      | ~ m1_yellow_0(B_13,A_11)
      | ~ l1_orders_2(B_13)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_192,plain,(
    ! [B_98,A_99,C_100] :
      ( k2_partfun1(u1_struct_0(B_98),u1_struct_0(A_99),u1_waybel_0(A_99,B_98),u1_struct_0(C_100)) = u1_waybel_0(A_99,C_100)
      | ~ m1_yellow_6(C_100,A_99,B_98)
      | ~ l1_waybel_0(C_100,A_99)
      | ~ l1_waybel_0(B_98,A_99)
      | ~ l1_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(u1_waybel_0(A_17,B_18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_18),u1_struct_0(A_17))))
      | ~ l1_waybel_0(B_18,A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_151,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k2_partfun1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    ! [B_18,A_17,D_83] :
      ( k2_partfun1(u1_struct_0(B_18),u1_struct_0(A_17),u1_waybel_0(A_17,B_18),D_83) = k7_relat_1(u1_waybel_0(A_17,B_18),D_83)
      | ~ v1_funct_1(u1_waybel_0(A_17,B_18))
      | ~ l1_waybel_0(B_18,A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_273,plain,(
    ! [A_125,B_126,C_127] :
      ( k7_relat_1(u1_waybel_0(A_125,B_126),u1_struct_0(C_127)) = u1_waybel_0(A_125,C_127)
      | ~ v1_funct_1(u1_waybel_0(A_125,B_126))
      | ~ l1_waybel_0(B_126,A_125)
      | ~ l1_struct_0(A_125)
      | ~ m1_yellow_6(C_127,A_125,B_126)
      | ~ l1_waybel_0(C_127,A_125)
      | ~ l1_waybel_0(B_126,A_125)
      | ~ l1_struct_0(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_154])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( k7_relat_1(k7_relat_1(C_3,B_2),A_1) = k7_relat_1(C_3,A_1)
      | ~ r1_tarski(A_1,B_2)
      | ~ v1_funct_1(C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2842,plain,(
    ! [A_226,C_227,A_228,B_229] :
      ( k7_relat_1(u1_waybel_0(A_226,C_227),A_228) = k7_relat_1(u1_waybel_0(A_226,B_229),A_228)
      | ~ r1_tarski(A_228,u1_struct_0(C_227))
      | ~ v1_funct_1(u1_waybel_0(A_226,B_229))
      | ~ v1_relat_1(u1_waybel_0(A_226,B_229))
      | ~ v1_funct_1(u1_waybel_0(A_226,B_229))
      | ~ l1_waybel_0(B_229,A_226)
      | ~ l1_struct_0(A_226)
      | ~ m1_yellow_6(C_227,A_226,B_229)
      | ~ l1_waybel_0(C_227,A_226)
      | ~ l1_waybel_0(B_229,A_226)
      | ~ l1_struct_0(A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_2])).

tff(c_2846,plain,(
    ! [A_230,B_231,B_232,A_233] :
      ( k7_relat_1(u1_waybel_0(A_230,B_231),u1_struct_0(B_232)) = k7_relat_1(u1_waybel_0(A_230,A_233),u1_struct_0(B_232))
      | ~ v1_relat_1(u1_waybel_0(A_230,B_231))
      | ~ v1_funct_1(u1_waybel_0(A_230,B_231))
      | ~ m1_yellow_6(A_233,A_230,B_231)
      | ~ l1_waybel_0(A_233,A_230)
      | ~ l1_waybel_0(B_231,A_230)
      | ~ l1_struct_0(A_230)
      | ~ m1_yellow_0(B_232,A_233)
      | ~ l1_orders_2(B_232)
      | ~ l1_orders_2(A_233) ) ),
    inference(resolution,[status(thm)],[c_14,c_2842])).

tff(c_2850,plain,(
    ! [B_232] :
      ( k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_232)) = k7_relat_1(u1_waybel_0('#skF_1','#skF_4'),u1_struct_0(B_232))
      | ~ v1_relat_1(u1_waybel_0('#skF_1','#skF_3'))
      | ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_3'))
      | ~ l1_waybel_0('#skF_4','#skF_1')
      | ~ l1_waybel_0('#skF_3','#skF_1')
      | ~ l1_struct_0('#skF_1')
      | ~ m1_yellow_0(B_232,'#skF_4')
      | ~ l1_orders_2(B_232)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_2846])).

tff(c_2856,plain,(
    ! [B_232] :
      ( k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_232)) = k7_relat_1(u1_waybel_0('#skF_1','#skF_4'),u1_struct_0(B_232))
      | ~ v1_relat_1(u1_waybel_0('#skF_1','#skF_3'))
      | ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_3'))
      | ~ m1_yellow_0(B_232,'#skF_4')
      | ~ l1_orders_2(B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42,c_62,c_73,c_2850])).

tff(c_2867,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2856])).

tff(c_2870,plain,
    ( ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_2867])).

tff(c_2874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62,c_2870])).

tff(c_2876,plain,(
    v1_funct_1(u1_waybel_0('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2856])).

tff(c_198,plain,(
    ! [A_99,B_98,C_100] :
      ( k7_relat_1(u1_waybel_0(A_99,B_98),u1_struct_0(C_100)) = u1_waybel_0(A_99,C_100)
      | ~ v1_funct_1(u1_waybel_0(A_99,B_98))
      | ~ l1_waybel_0(B_98,A_99)
      | ~ l1_struct_0(A_99)
      | ~ m1_yellow_6(C_100,A_99,B_98)
      | ~ l1_waybel_0(C_100,A_99)
      | ~ l1_waybel_0(B_98,A_99)
      | ~ l1_struct_0(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_154])).

tff(c_68,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_16])).

tff(c_71,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_68])).

tff(c_2848,plain,(
    ! [B_232] :
      ( k7_relat_1(u1_waybel_0('#skF_1','#skF_2'),u1_struct_0(B_232)) = k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_232))
      | ~ v1_relat_1(u1_waybel_0('#skF_1','#skF_2'))
      | ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_2'))
      | ~ l1_waybel_0('#skF_3','#skF_1')
      | ~ l1_waybel_0('#skF_2','#skF_1')
      | ~ l1_struct_0('#skF_1')
      | ~ m1_yellow_0(B_232,'#skF_3')
      | ~ l1_orders_2(B_232)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_2846])).

tff(c_2853,plain,(
    ! [B_232] :
      ( k7_relat_1(u1_waybel_0('#skF_1','#skF_2'),u1_struct_0(B_232)) = k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_232))
      | ~ v1_relat_1(u1_waybel_0('#skF_1','#skF_2'))
      | ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_2'))
      | ~ m1_yellow_0(B_232,'#skF_3')
      | ~ l1_orders_2(B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_42,c_40,c_62,c_2848])).

tff(c_2857,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2853])).

tff(c_2860,plain,
    ( ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_2857])).

tff(c_2864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2860])).

tff(c_2866,plain,(
    v1_funct_1(u1_waybel_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2853])).

tff(c_126,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(u1_waybel_0(A_73,B_74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_74),u1_struct_0(A_73))))
      | ~ l1_waybel_0(B_74,A_73)
      | ~ l1_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    ! [A_73,B_74] :
      ( v1_relat_1(u1_waybel_0(A_73,B_74))
      | ~ l1_waybel_0(B_74,A_73)
      | ~ l1_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_126,c_6])).

tff(c_2865,plain,(
    ! [B_232] :
      ( ~ v1_relat_1(u1_waybel_0('#skF_1','#skF_2'))
      | k7_relat_1(u1_waybel_0('#skF_1','#skF_2'),u1_struct_0(B_232)) = k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_232))
      | ~ m1_yellow_0(B_232,'#skF_3')
      | ~ l1_orders_2(B_232) ) ),
    inference(splitRight,[status(thm)],[c_2853])).

tff(c_2877,plain,(
    ~ v1_relat_1(u1_waybel_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2865])).

tff(c_2884,plain,
    ( ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_130,c_2877])).

tff(c_2888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2884])).

tff(c_2891,plain,(
    ! [B_238] :
      ( k7_relat_1(u1_waybel_0('#skF_1','#skF_2'),u1_struct_0(B_238)) = k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_238))
      | ~ m1_yellow_0(B_238,'#skF_3')
      | ~ l1_orders_2(B_238) ) ),
    inference(splitRight,[status(thm)],[c_2865])).

tff(c_247,plain,(
    ! [C_110,A_111,B_112] :
      ( m1_yellow_6(C_110,A_111,B_112)
      | k2_partfun1(u1_struct_0(B_112),u1_struct_0(A_111),u1_waybel_0(A_111,B_112),u1_struct_0(C_110)) != u1_waybel_0(A_111,C_110)
      | ~ m1_yellow_0(C_110,B_112)
      | ~ l1_waybel_0(C_110,A_111)
      | ~ l1_waybel_0(B_112,A_111)
      | ~ l1_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_254,plain,(
    ! [C_110,A_17,B_18] :
      ( m1_yellow_6(C_110,A_17,B_18)
      | k7_relat_1(u1_waybel_0(A_17,B_18),u1_struct_0(C_110)) != u1_waybel_0(A_17,C_110)
      | ~ m1_yellow_0(C_110,B_18)
      | ~ l1_waybel_0(C_110,A_17)
      | ~ l1_waybel_0(B_18,A_17)
      | ~ l1_struct_0(A_17)
      | ~ v1_funct_1(u1_waybel_0(A_17,B_18))
      | ~ l1_waybel_0(B_18,A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_247])).

tff(c_2966,plain,(
    ! [B_238] :
      ( m1_yellow_6(B_238,'#skF_1','#skF_2')
      | k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_238)) != u1_waybel_0('#skF_1',B_238)
      | ~ m1_yellow_0(B_238,'#skF_2')
      | ~ l1_waybel_0(B_238,'#skF_1')
      | ~ l1_waybel_0('#skF_2','#skF_1')
      | ~ l1_struct_0('#skF_1')
      | ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_2'))
      | ~ l1_waybel_0('#skF_2','#skF_1')
      | ~ l1_struct_0('#skF_1')
      | ~ m1_yellow_0(B_238,'#skF_3')
      | ~ l1_orders_2(B_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2891,c_254])).

tff(c_8134,plain,(
    ! [B_297] :
      ( m1_yellow_6(B_297,'#skF_1','#skF_2')
      | k7_relat_1(u1_waybel_0('#skF_1','#skF_3'),u1_struct_0(B_297)) != u1_waybel_0('#skF_1',B_297)
      | ~ m1_yellow_0(B_297,'#skF_2')
      | ~ l1_waybel_0(B_297,'#skF_1')
      | ~ m1_yellow_0(B_297,'#skF_3')
      | ~ l1_orders_2(B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2866,c_42,c_40,c_2966])).

tff(c_8147,plain,(
    ! [C_100] :
      ( m1_yellow_6(C_100,'#skF_1','#skF_2')
      | ~ m1_yellow_0(C_100,'#skF_2')
      | ~ m1_yellow_0(C_100,'#skF_3')
      | ~ l1_orders_2(C_100)
      | ~ v1_funct_1(u1_waybel_0('#skF_1','#skF_3'))
      | ~ m1_yellow_6(C_100,'#skF_1','#skF_3')
      | ~ l1_waybel_0(C_100,'#skF_1')
      | ~ l1_waybel_0('#skF_3','#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_8134])).

tff(c_8153,plain,(
    ! [C_298] :
      ( m1_yellow_6(C_298,'#skF_1','#skF_2')
      | ~ m1_yellow_0(C_298,'#skF_2')
      | ~ m1_yellow_0(C_298,'#skF_3')
      | ~ l1_orders_2(C_298)
      | ~ m1_yellow_6(C_298,'#skF_1','#skF_3')
      | ~ l1_waybel_0(C_298,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62,c_2876,c_8147])).

tff(c_34,plain,(
    ~ m1_yellow_6('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8170,plain,
    ( ~ m1_yellow_0('#skF_4','#skF_2')
    | ~ m1_yellow_0('#skF_4','#skF_3')
    | ~ l1_orders_2('#skF_4')
    | ~ m1_yellow_6('#skF_4','#skF_1','#skF_3')
    | ~ l1_waybel_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_8153,c_34])).

tff(c_8185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_36,c_79,c_144,c_162,c_8170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:34:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.05/3.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.05/3.96  
% 11.05/3.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.05/3.96  %$ v1_funct_2 > m1_yellow_6 > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.05/3.96  
% 11.05/3.96  %Foreground sorts:
% 11.05/3.96  
% 11.05/3.96  
% 11.05/3.96  %Background operators:
% 11.05/3.96  
% 11.05/3.96  
% 11.05/3.96  %Foreground operators:
% 11.05/3.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.05/3.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.05/3.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.05/3.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.05/3.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.05/3.96  tff('#skF_2', type, '#skF_2': $i).
% 11.05/3.96  tff('#skF_3', type, '#skF_3': $i).
% 11.05/3.96  tff('#skF_1', type, '#skF_1': $i).
% 11.05/3.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.05/3.96  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 11.05/3.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.05/3.96  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 11.05/3.96  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 11.05/3.96  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 11.05/3.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.05/3.96  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 11.05/3.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.05/3.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.05/3.96  tff('#skF_4', type, '#skF_4': $i).
% 11.05/3.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.05/3.96  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 11.05/3.96  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 11.05/3.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.05/3.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.05/3.96  
% 11.05/3.98  tff(f_120, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (![D]: (m1_yellow_6(D, A, C) => m1_yellow_6(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_6)).
% 11.05/3.98  tff(f_96, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 11.05/3.98  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 11.05/3.98  tff(f_87, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (l1_waybel_0(C, A) => (m1_yellow_6(C, A, B) <=> (m1_yellow_0(C, B) & (u1_waybel_0(A, C) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_6)).
% 11.05/3.98  tff(f_106, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => (![C]: (m1_yellow_0(C, B) => m1_yellow_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_yellow_6)).
% 11.05/3.98  tff(f_73, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 11.05/3.98  tff(f_56, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 11.05/3.98  tff(f_45, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 11.05/3.98  tff(f_35, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A)) & (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_funct_1)).
% 11.05/3.98  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.05/3.98  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.05/3.98  tff(c_40, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.05/3.98  tff(c_38, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.05/3.98  tff(c_53, plain, (![C_58, A_59, B_60]: (l1_waybel_0(C_58, A_59) | ~m1_yellow_6(C_58, A_59, B_60) | ~l1_waybel_0(B_60, A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.05/3.98  tff(c_56, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_53])).
% 11.05/3.98  tff(c_62, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_56])).
% 11.05/3.98  tff(c_36, plain, (m1_yellow_6('#skF_4', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.05/3.98  tff(c_59, plain, (l1_waybel_0('#skF_4', '#skF_1') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_53])).
% 11.05/3.98  tff(c_65, plain, (l1_waybel_0('#skF_4', '#skF_1') | ~l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_59])).
% 11.05/3.98  tff(c_73, plain, (l1_waybel_0('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_65])).
% 11.05/3.98  tff(c_16, plain, (![B_16, A_14]: (l1_orders_2(B_16) | ~l1_waybel_0(B_16, A_14) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.05/3.98  tff(c_76, plain, (l1_orders_2('#skF_4') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_73, c_16])).
% 11.05/3.98  tff(c_79, plain, (l1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_76])).
% 11.05/3.98  tff(c_132, plain, (![C_77, B_78, A_79]: (m1_yellow_0(C_77, B_78) | ~m1_yellow_6(C_77, A_79, B_78) | ~l1_waybel_0(C_77, A_79) | ~l1_waybel_0(B_78, A_79) | ~l1_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.05/3.98  tff(c_138, plain, (m1_yellow_0('#skF_4', '#skF_3') | ~l1_waybel_0('#skF_4', '#skF_1') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_132])).
% 11.05/3.98  tff(c_144, plain, (m1_yellow_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62, c_73, c_138])).
% 11.05/3.98  tff(c_43, plain, (![B_48, A_49]: (l1_orders_2(B_48) | ~l1_waybel_0(B_48, A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.05/3.98  tff(c_46, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_43])).
% 11.05/3.98  tff(c_49, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 11.05/3.98  tff(c_135, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_132])).
% 11.05/3.98  tff(c_141, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_62, c_135])).
% 11.05/3.98  tff(c_32, plain, (![C_36, A_30, B_34]: (m1_yellow_0(C_36, A_30) | ~m1_yellow_0(C_36, B_34) | ~m1_yellow_0(B_34, A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.05/3.98  tff(c_156, plain, (![A_85]: (m1_yellow_0('#skF_4', A_85) | ~m1_yellow_0('#skF_3', A_85) | ~l1_orders_2(A_85))), inference(resolution, [status(thm)], [c_144, c_32])).
% 11.05/3.98  tff(c_159, plain, (m1_yellow_0('#skF_4', '#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_141, c_156])).
% 11.05/3.98  tff(c_162, plain, (m1_yellow_0('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_159])).
% 11.05/3.98  tff(c_22, plain, (![A_17, B_18]: (v1_funct_1(u1_waybel_0(A_17, B_18)) | ~l1_waybel_0(B_18, A_17) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.05/3.98  tff(c_14, plain, (![B_13, A_11]: (r1_tarski(u1_struct_0(B_13), u1_struct_0(A_11)) | ~m1_yellow_0(B_13, A_11) | ~l1_orders_2(B_13) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.05/3.98  tff(c_192, plain, (![B_98, A_99, C_100]: (k2_partfun1(u1_struct_0(B_98), u1_struct_0(A_99), u1_waybel_0(A_99, B_98), u1_struct_0(C_100))=u1_waybel_0(A_99, C_100) | ~m1_yellow_6(C_100, A_99, B_98) | ~l1_waybel_0(C_100, A_99) | ~l1_waybel_0(B_98, A_99) | ~l1_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.05/3.98  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(u1_waybel_0(A_17, B_18), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_18), u1_struct_0(A_17)))) | ~l1_waybel_0(B_18, A_17) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.05/3.98  tff(c_151, plain, (![A_80, B_81, C_82, D_83]: (k2_partfun1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.05/3.98  tff(c_154, plain, (![B_18, A_17, D_83]: (k2_partfun1(u1_struct_0(B_18), u1_struct_0(A_17), u1_waybel_0(A_17, B_18), D_83)=k7_relat_1(u1_waybel_0(A_17, B_18), D_83) | ~v1_funct_1(u1_waybel_0(A_17, B_18)) | ~l1_waybel_0(B_18, A_17) | ~l1_struct_0(A_17))), inference(resolution, [status(thm)], [c_18, c_151])).
% 11.05/3.98  tff(c_273, plain, (![A_125, B_126, C_127]: (k7_relat_1(u1_waybel_0(A_125, B_126), u1_struct_0(C_127))=u1_waybel_0(A_125, C_127) | ~v1_funct_1(u1_waybel_0(A_125, B_126)) | ~l1_waybel_0(B_126, A_125) | ~l1_struct_0(A_125) | ~m1_yellow_6(C_127, A_125, B_126) | ~l1_waybel_0(C_127, A_125) | ~l1_waybel_0(B_126, A_125) | ~l1_struct_0(A_125))), inference(superposition, [status(thm), theory('equality')], [c_192, c_154])).
% 11.05/3.98  tff(c_2, plain, (![C_3, B_2, A_1]: (k7_relat_1(k7_relat_1(C_3, B_2), A_1)=k7_relat_1(C_3, A_1) | ~r1_tarski(A_1, B_2) | ~v1_funct_1(C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.05/3.98  tff(c_2842, plain, (![A_226, C_227, A_228, B_229]: (k7_relat_1(u1_waybel_0(A_226, C_227), A_228)=k7_relat_1(u1_waybel_0(A_226, B_229), A_228) | ~r1_tarski(A_228, u1_struct_0(C_227)) | ~v1_funct_1(u1_waybel_0(A_226, B_229)) | ~v1_relat_1(u1_waybel_0(A_226, B_229)) | ~v1_funct_1(u1_waybel_0(A_226, B_229)) | ~l1_waybel_0(B_229, A_226) | ~l1_struct_0(A_226) | ~m1_yellow_6(C_227, A_226, B_229) | ~l1_waybel_0(C_227, A_226) | ~l1_waybel_0(B_229, A_226) | ~l1_struct_0(A_226))), inference(superposition, [status(thm), theory('equality')], [c_273, c_2])).
% 11.05/3.98  tff(c_2846, plain, (![A_230, B_231, B_232, A_233]: (k7_relat_1(u1_waybel_0(A_230, B_231), u1_struct_0(B_232))=k7_relat_1(u1_waybel_0(A_230, A_233), u1_struct_0(B_232)) | ~v1_relat_1(u1_waybel_0(A_230, B_231)) | ~v1_funct_1(u1_waybel_0(A_230, B_231)) | ~m1_yellow_6(A_233, A_230, B_231) | ~l1_waybel_0(A_233, A_230) | ~l1_waybel_0(B_231, A_230) | ~l1_struct_0(A_230) | ~m1_yellow_0(B_232, A_233) | ~l1_orders_2(B_232) | ~l1_orders_2(A_233))), inference(resolution, [status(thm)], [c_14, c_2842])).
% 11.05/3.98  tff(c_2850, plain, (![B_232]: (k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_232))=k7_relat_1(u1_waybel_0('#skF_1', '#skF_4'), u1_struct_0(B_232)) | ~v1_relat_1(u1_waybel_0('#skF_1', '#skF_3')) | ~v1_funct_1(u1_waybel_0('#skF_1', '#skF_3')) | ~l1_waybel_0('#skF_4', '#skF_1') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_struct_0('#skF_1') | ~m1_yellow_0(B_232, '#skF_4') | ~l1_orders_2(B_232) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_2846])).
% 11.05/3.98  tff(c_2856, plain, (![B_232]: (k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_232))=k7_relat_1(u1_waybel_0('#skF_1', '#skF_4'), u1_struct_0(B_232)) | ~v1_relat_1(u1_waybel_0('#skF_1', '#skF_3')) | ~v1_funct_1(u1_waybel_0('#skF_1', '#skF_3')) | ~m1_yellow_0(B_232, '#skF_4') | ~l1_orders_2(B_232))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42, c_62, c_73, c_2850])).
% 11.05/3.98  tff(c_2867, plain, (~v1_funct_1(u1_waybel_0('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2856])).
% 11.05/3.98  tff(c_2870, plain, (~l1_waybel_0('#skF_3', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_2867])).
% 11.05/3.98  tff(c_2874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_62, c_2870])).
% 11.05/3.98  tff(c_2876, plain, (v1_funct_1(u1_waybel_0('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_2856])).
% 11.05/3.98  tff(c_198, plain, (![A_99, B_98, C_100]: (k7_relat_1(u1_waybel_0(A_99, B_98), u1_struct_0(C_100))=u1_waybel_0(A_99, C_100) | ~v1_funct_1(u1_waybel_0(A_99, B_98)) | ~l1_waybel_0(B_98, A_99) | ~l1_struct_0(A_99) | ~m1_yellow_6(C_100, A_99, B_98) | ~l1_waybel_0(C_100, A_99) | ~l1_waybel_0(B_98, A_99) | ~l1_struct_0(A_99))), inference(superposition, [status(thm), theory('equality')], [c_192, c_154])).
% 11.05/3.98  tff(c_68, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_16])).
% 11.05/3.98  tff(c_71, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_68])).
% 11.05/3.98  tff(c_2848, plain, (![B_232]: (k7_relat_1(u1_waybel_0('#skF_1', '#skF_2'), u1_struct_0(B_232))=k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_232)) | ~v1_relat_1(u1_waybel_0('#skF_1', '#skF_2')) | ~v1_funct_1(u1_waybel_0('#skF_1', '#skF_2')) | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1') | ~m1_yellow_0(B_232, '#skF_3') | ~l1_orders_2(B_232) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_2846])).
% 11.05/3.98  tff(c_2853, plain, (![B_232]: (k7_relat_1(u1_waybel_0('#skF_1', '#skF_2'), u1_struct_0(B_232))=k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_232)) | ~v1_relat_1(u1_waybel_0('#skF_1', '#skF_2')) | ~v1_funct_1(u1_waybel_0('#skF_1', '#skF_2')) | ~m1_yellow_0(B_232, '#skF_3') | ~l1_orders_2(B_232))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_42, c_40, c_62, c_2848])).
% 11.05/3.98  tff(c_2857, plain, (~v1_funct_1(u1_waybel_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2853])).
% 11.05/3.98  tff(c_2860, plain, (~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_2857])).
% 11.05/3.98  tff(c_2864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2860])).
% 11.05/3.98  tff(c_2866, plain, (v1_funct_1(u1_waybel_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2853])).
% 11.05/3.98  tff(c_126, plain, (![A_73, B_74]: (m1_subset_1(u1_waybel_0(A_73, B_74), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_74), u1_struct_0(A_73)))) | ~l1_waybel_0(B_74, A_73) | ~l1_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.05/3.98  tff(c_6, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.05/3.98  tff(c_130, plain, (![A_73, B_74]: (v1_relat_1(u1_waybel_0(A_73, B_74)) | ~l1_waybel_0(B_74, A_73) | ~l1_struct_0(A_73))), inference(resolution, [status(thm)], [c_126, c_6])).
% 11.05/3.98  tff(c_2865, plain, (![B_232]: (~v1_relat_1(u1_waybel_0('#skF_1', '#skF_2')) | k7_relat_1(u1_waybel_0('#skF_1', '#skF_2'), u1_struct_0(B_232))=k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_232)) | ~m1_yellow_0(B_232, '#skF_3') | ~l1_orders_2(B_232))), inference(splitRight, [status(thm)], [c_2853])).
% 11.05/3.98  tff(c_2877, plain, (~v1_relat_1(u1_waybel_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2865])).
% 11.05/3.98  tff(c_2884, plain, (~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_130, c_2877])).
% 11.05/3.98  tff(c_2888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2884])).
% 11.05/3.98  tff(c_2891, plain, (![B_238]: (k7_relat_1(u1_waybel_0('#skF_1', '#skF_2'), u1_struct_0(B_238))=k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_238)) | ~m1_yellow_0(B_238, '#skF_3') | ~l1_orders_2(B_238))), inference(splitRight, [status(thm)], [c_2865])).
% 11.05/3.98  tff(c_247, plain, (![C_110, A_111, B_112]: (m1_yellow_6(C_110, A_111, B_112) | k2_partfun1(u1_struct_0(B_112), u1_struct_0(A_111), u1_waybel_0(A_111, B_112), u1_struct_0(C_110))!=u1_waybel_0(A_111, C_110) | ~m1_yellow_0(C_110, B_112) | ~l1_waybel_0(C_110, A_111) | ~l1_waybel_0(B_112, A_111) | ~l1_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.05/3.98  tff(c_254, plain, (![C_110, A_17, B_18]: (m1_yellow_6(C_110, A_17, B_18) | k7_relat_1(u1_waybel_0(A_17, B_18), u1_struct_0(C_110))!=u1_waybel_0(A_17, C_110) | ~m1_yellow_0(C_110, B_18) | ~l1_waybel_0(C_110, A_17) | ~l1_waybel_0(B_18, A_17) | ~l1_struct_0(A_17) | ~v1_funct_1(u1_waybel_0(A_17, B_18)) | ~l1_waybel_0(B_18, A_17) | ~l1_struct_0(A_17))), inference(superposition, [status(thm), theory('equality')], [c_154, c_247])).
% 11.05/3.98  tff(c_2966, plain, (![B_238]: (m1_yellow_6(B_238, '#skF_1', '#skF_2') | k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_238))!=u1_waybel_0('#skF_1', B_238) | ~m1_yellow_0(B_238, '#skF_2') | ~l1_waybel_0(B_238, '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1') | ~v1_funct_1(u1_waybel_0('#skF_1', '#skF_2')) | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1') | ~m1_yellow_0(B_238, '#skF_3') | ~l1_orders_2(B_238))), inference(superposition, [status(thm), theory('equality')], [c_2891, c_254])).
% 11.05/3.98  tff(c_8134, plain, (![B_297]: (m1_yellow_6(B_297, '#skF_1', '#skF_2') | k7_relat_1(u1_waybel_0('#skF_1', '#skF_3'), u1_struct_0(B_297))!=u1_waybel_0('#skF_1', B_297) | ~m1_yellow_0(B_297, '#skF_2') | ~l1_waybel_0(B_297, '#skF_1') | ~m1_yellow_0(B_297, '#skF_3') | ~l1_orders_2(B_297))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2866, c_42, c_40, c_2966])).
% 11.05/3.98  tff(c_8147, plain, (![C_100]: (m1_yellow_6(C_100, '#skF_1', '#skF_2') | ~m1_yellow_0(C_100, '#skF_2') | ~m1_yellow_0(C_100, '#skF_3') | ~l1_orders_2(C_100) | ~v1_funct_1(u1_waybel_0('#skF_1', '#skF_3')) | ~m1_yellow_6(C_100, '#skF_1', '#skF_3') | ~l1_waybel_0(C_100, '#skF_1') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_198, c_8134])).
% 11.05/3.98  tff(c_8153, plain, (![C_298]: (m1_yellow_6(C_298, '#skF_1', '#skF_2') | ~m1_yellow_0(C_298, '#skF_2') | ~m1_yellow_0(C_298, '#skF_3') | ~l1_orders_2(C_298) | ~m1_yellow_6(C_298, '#skF_1', '#skF_3') | ~l1_waybel_0(C_298, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62, c_2876, c_8147])).
% 11.05/3.98  tff(c_34, plain, (~m1_yellow_6('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.05/3.98  tff(c_8170, plain, (~m1_yellow_0('#skF_4', '#skF_2') | ~m1_yellow_0('#skF_4', '#skF_3') | ~l1_orders_2('#skF_4') | ~m1_yellow_6('#skF_4', '#skF_1', '#skF_3') | ~l1_waybel_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_8153, c_34])).
% 11.05/3.98  tff(c_8185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_36, c_79, c_144, c_162, c_8170])).
% 11.05/3.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.05/3.98  
% 11.05/3.98  Inference rules
% 11.05/3.98  ----------------------
% 11.05/3.98  #Ref     : 0
% 11.05/3.98  #Sup     : 2275
% 11.05/3.98  #Fact    : 0
% 11.05/3.98  #Define  : 0
% 11.05/3.98  #Split   : 11
% 11.05/3.98  #Chain   : 0
% 11.05/3.98  #Close   : 0
% 11.05/3.98  
% 11.05/3.98  Ordering : KBO
% 11.05/3.98  
% 11.05/3.98  Simplification rules
% 11.05/3.98  ----------------------
% 11.05/3.98  #Subsume      : 223
% 11.05/3.98  #Demod        : 1431
% 11.05/3.98  #Tautology    : 121
% 11.05/3.98  #SimpNegUnit  : 0
% 11.05/3.98  #BackRed      : 0
% 11.05/3.98  
% 11.05/3.98  #Partial instantiations: 0
% 11.05/3.98  #Strategies tried      : 1
% 11.05/3.98  
% 11.05/3.98  Timing (in seconds)
% 11.05/3.98  ----------------------
% 11.05/3.98  Preprocessing        : 0.34
% 11.05/3.98  Parsing              : 0.19
% 11.05/3.98  CNF conversion       : 0.02
% 11.05/3.98  Main loop            : 2.82
% 11.05/3.98  Inferencing          : 0.71
% 11.05/3.98  Reduction            : 0.72
% 11.05/3.98  Demodulation         : 0.51
% 11.05/3.98  BG Simplification    : 0.15
% 11.05/3.98  Subsumption          : 1.14
% 11.05/3.98  Abstraction          : 0.17
% 11.05/3.98  MUC search           : 0.00
% 11.05/3.98  Cooper               : 0.00
% 11.05/3.98  Total                : 3.20
% 11.05/3.98  Index Insertion      : 0.00
% 11.05/3.98  Index Deletion       : 0.00
% 11.05/3.98  Index Matching       : 0.00
% 11.05/3.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
