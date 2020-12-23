%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:42 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 672 expanded)
%              Number of leaves         :   35 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          :  447 (2954 expanded)
%              Number of equality atoms :   39 ( 132 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_orders_2(A,B,C)
                <=> r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1060,plain,(
    ! [A_162,B_163] :
      ( k6_domain_1(A_162,B_163) = k1_tarski(B_163)
      | ~ m1_subset_1(B_163,A_162)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1067,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_1060])).

tff(c_1069,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1067])).

tff(c_34,plain,(
    ! [A_28,B_30] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_28),B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_30,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | ~ v3_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1189,plain,(
    ! [D_200,B_201,C_202] :
      ( r2_hidden('#skF_4'(D_200,B_201,C_202,D_200),C_202)
      | r2_hidden(D_200,a_2_1_orders_2(B_201,C_202))
      | ~ m1_subset_1(D_200,u1_struct_0(B_201))
      | ~ m1_subset_1(C_202,k1_zfmisc_1(u1_struct_0(B_201)))
      | ~ l1_orders_2(B_201)
      | ~ v5_orders_2(B_201)
      | ~ v4_orders_2(B_201)
      | ~ v3_orders_2(B_201)
      | v2_struct_0(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1208,plain,(
    ! [D_218,A_219,B_220] :
      ( r2_hidden('#skF_4'(D_218,A_219,k6_domain_1(u1_struct_0(A_219),B_220),D_218),k6_domain_1(u1_struct_0(A_219),B_220))
      | r2_hidden(D_218,a_2_1_orders_2(A_219,k6_domain_1(u1_struct_0(A_219),B_220)))
      | ~ m1_subset_1(D_218,u1_struct_0(A_219))
      | ~ v5_orders_2(A_219)
      | ~ v4_orders_2(A_219)
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ l1_orders_2(A_219)
      | ~ v3_orders_2(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_34,c_1189])).

tff(c_1110,plain,(
    ! [A_178,B_179] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_178),B_179),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v3_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_16,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1117,plain,(
    ! [A_178,A_7,B_179] :
      ( ~ v1_xboole_0(u1_struct_0(A_178))
      | ~ r2_hidden(A_7,k6_domain_1(u1_struct_0(A_178),B_179))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v3_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_1110,c_16])).

tff(c_1213,plain,(
    ! [A_221,D_222,B_223] :
      ( ~ v1_xboole_0(u1_struct_0(A_221))
      | r2_hidden(D_222,a_2_1_orders_2(A_221,k6_domain_1(u1_struct_0(A_221),B_223)))
      | ~ m1_subset_1(D_222,u1_struct_0(A_221))
      | ~ v5_orders_2(A_221)
      | ~ v4_orders_2(A_221)
      | ~ m1_subset_1(B_223,u1_struct_0(A_221))
      | ~ l1_orders_2(A_221)
      | ~ v3_orders_2(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_1208,c_1117])).

tff(c_1118,plain,(
    ! [A_180,B_181] :
      ( k2_orders_2(A_180,B_181) = a_2_1_orders_2(A_180,B_181)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_orders_2(A_180)
      | ~ v5_orders_2(A_180)
      | ~ v4_orders_2(A_180)
      | ~ v3_orders_2(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1149,plain,(
    ! [A_193,B_194] :
      ( k2_orders_2(A_193,k6_domain_1(u1_struct_0(A_193),B_194)) = a_2_1_orders_2(A_193,k6_domain_1(u1_struct_0(A_193),B_194))
      | ~ v5_orders_2(A_193)
      | ~ v4_orders_2(A_193)
      | ~ m1_subset_1(B_194,u1_struct_0(A_193))
      | ~ l1_orders_2(A_193)
      | ~ v3_orders_2(A_193)
      | v2_struct_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_34,c_1118])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_71,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_86,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_88,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_149,plain,(
    ! [A_66,B_67] :
      ( k2_orders_2(A_66,B_67) = a_2_1_orders_2(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_164,plain,(
    ! [A_73,B_74] :
      ( k2_orders_2(A_73,k6_domain_1(u1_struct_0(A_73),B_74)) = a_2_1_orders_2(A_73,k6_domain_1(u1_struct_0(A_73),B_74))
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_60,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_92,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_60])).

tff(c_173,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_92])).

tff(c_179,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_48,c_46,c_173])).

tff(c_180,plain,(
    r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_179])).

tff(c_28,plain,(
    ! [A_13,B_14,C_15] :
      ( '#skF_3'(A_13,B_14,C_15) = A_13
      | ~ r2_hidden(A_13,a_2_1_orders_2(B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(B_14)))
      | ~ l1_orders_2(B_14)
      | ~ v5_orders_2(B_14)
      | ~ v4_orders_2(B_14)
      | ~ v3_orders_2(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_183,plain,
    ( '#skF_3'('#skF_6','#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_28])).

tff(c_186,plain,
    ( '#skF_3'('#skF_6','#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_183])).

tff(c_187,plain,
    ( '#skF_3'('#skF_6','#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_186])).

tff(c_188,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_191,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_188])).

tff(c_194,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_191])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_194])).

tff(c_198,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_206,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_7,k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_198,c_16])).

tff(c_214,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_206])).

tff(c_318,plain,(
    ! [D_85,B_86,C_87] :
      ( r2_hidden('#skF_4'(D_85,B_86,C_87,D_85),C_87)
      | r2_hidden(D_85,a_2_1_orders_2(B_86,C_87))
      | ~ m1_subset_1(D_85,u1_struct_0(B_86))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(B_86)))
      | ~ l1_orders_2(B_86)
      | ~ v5_orders_2(B_86)
      | ~ v4_orders_2(B_86)
      | ~ v3_orders_2(B_86)
      | v2_struct_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_320,plain,(
    ! [D_85] :
      ( r2_hidden('#skF_4'(D_85,'#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'),D_85),k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))
      | r2_hidden(D_85,a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
      | ~ m1_subset_1(D_85,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_198,c_318])).

tff(c_325,plain,(
    ! [D_85] :
      ( r2_hidden('#skF_4'(D_85,'#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'),D_85),k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))
      | r2_hidden(D_85,a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
      | ~ m1_subset_1(D_85,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_320])).

tff(c_328,plain,(
    ! [D_88] :
      ( r2_hidden(D_88,a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
      | ~ m1_subset_1(D_88,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_214,c_325])).

tff(c_18,plain,(
    ! [A_10,B_12] :
      ( k2_orders_2(A_10,B_12) = a_2_1_orders_2(A_10,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,
    ( k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) = a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_198,c_18])).

tff(c_209,plain,
    ( k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) = a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_201])).

tff(c_210,plain,(
    k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) = a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_209])).

tff(c_38,plain,(
    ! [B_33,A_31] :
      ( ~ r2_hidden(B_33,k2_orders_2(A_31,k6_domain_1(u1_struct_0(A_31),B_33)))
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_249,plain,
    ( ~ r2_hidden('#skF_7',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_38])).

tff(c_260,plain,
    ( ~ r2_hidden('#skF_7',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_40,c_249])).

tff(c_261,plain,(
    ~ r2_hidden('#skF_7',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_260])).

tff(c_331,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_328,c_261])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_331])).

tff(c_342,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_405,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_101),B_102),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_416,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_405])).

tff(c_423,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_416])).

tff(c_424,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_423])).

tff(c_441,plain,(
    ! [A_103,B_104] :
      ( k2_orders_2(A_103,B_104) = a_2_1_orders_2(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_444,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_424,c_441])).

tff(c_453,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_444])).

tff(c_454,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_453])).

tff(c_348,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_60])).

tff(c_349,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_348])).

tff(c_460,plain,(
    r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_349])).

tff(c_506,plain,(
    ! [A_112,B_113,C_114] :
      ( '#skF_3'(A_112,B_113,C_114) = A_112
      | ~ r2_hidden(A_112,a_2_1_orders_2(B_113,C_114))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(B_113)))
      | ~ l1_orders_2(B_113)
      | ~ v5_orders_2(B_113)
      | ~ v4_orders_2(B_113)
      | ~ v3_orders_2(B_113)
      | v2_struct_0(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_508,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_460,c_506])).

tff(c_517,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_424,c_508])).

tff(c_518,plain,(
    '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_517])).

tff(c_991,plain,(
    ! [B_150,A_151,C_152,E_153] :
      ( r2_orders_2(B_150,'#skF_3'(A_151,B_150,C_152),E_153)
      | ~ r2_hidden(E_153,C_152)
      | ~ m1_subset_1(E_153,u1_struct_0(B_150))
      | ~ r2_hidden(A_151,a_2_1_orders_2(B_150,C_152))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ l1_orders_2(B_150)
      | ~ v5_orders_2(B_150)
      | ~ v4_orders_2(B_150)
      | ~ v3_orders_2(B_150)
      | v2_struct_0(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_993,plain,(
    ! [A_151,E_153] :
      ( r2_orders_2('#skF_5','#skF_3'(A_151,'#skF_5',k1_tarski('#skF_7')),E_153)
      | ~ r2_hidden(E_153,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_153,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_151,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_424,c_991])).

tff(c_1000,plain,(
    ! [A_151,E_153] :
      ( r2_orders_2('#skF_5','#skF_3'(A_151,'#skF_5',k1_tarski('#skF_7')),E_153)
      | ~ r2_hidden(E_153,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_153,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_151,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_993])).

tff(c_1007,plain,(
    ! [A_154,E_155] :
      ( r2_orders_2('#skF_5','#skF_3'(A_154,'#skF_5',k1_tarski('#skF_7')),E_155)
      | ~ r2_hidden(E_155,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_155,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_154,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1000])).

tff(c_1019,plain,(
    ! [E_155] :
      ( r2_orders_2('#skF_5','#skF_6',E_155)
      | ~ r2_hidden(E_155,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_155,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_1007])).

tff(c_1026,plain,(
    ! [E_156] :
      ( r2_orders_2('#skF_5','#skF_6',E_156)
      | ~ r2_hidden(E_156,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_156,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_1019])).

tff(c_1041,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_1026])).

tff(c_1047,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1041])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1047])).

tff(c_1050,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1158,plain,
    ( ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_1050])).

tff(c_1164,plain,
    ( ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_48,c_46,c_1158])).

tff(c_1165,plain,(
    ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1164])).

tff(c_1220,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1213,c_1165])).

tff(c_1230,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_48,c_46,c_42,c_1069,c_1220])).

tff(c_1232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1230])).

tff(c_1233,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1067])).

tff(c_1296,plain,(
    ! [A_238,B_239] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_238),B_239),k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ m1_subset_1(B_239,u1_struct_0(A_238))
      | ~ l1_orders_2(A_238)
      | ~ v3_orders_2(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1307,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1233,c_1296])).

tff(c_1314,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_1307])).

tff(c_1315,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1314])).

tff(c_1356,plain,(
    ! [A_243,B_244] :
      ( k2_orders_2(A_243,B_244) = a_2_1_orders_2(A_243,B_244)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_orders_2(A_243)
      | ~ v5_orders_2(A_243)
      | ~ v4_orders_2(A_243)
      | ~ v3_orders_2(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1359,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1315,c_1356])).

tff(c_1368,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1359])).

tff(c_1369,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1368])).

tff(c_1235,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_1050])).

tff(c_1375,plain,(
    ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1235])).

tff(c_1051,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1461,plain,(
    ! [D_258,B_259,C_260] :
      ( r2_hidden('#skF_4'(D_258,B_259,C_260,D_258),C_260)
      | r2_hidden(D_258,a_2_1_orders_2(B_259,C_260))
      | ~ m1_subset_1(D_258,u1_struct_0(B_259))
      | ~ m1_subset_1(C_260,k1_zfmisc_1(u1_struct_0(B_259)))
      | ~ l1_orders_2(B_259)
      | ~ v5_orders_2(B_259)
      | ~ v4_orders_2(B_259)
      | ~ v3_orders_2(B_259)
      | v2_struct_0(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1463,plain,(
    ! [D_258] :
      ( r2_hidden('#skF_4'(D_258,'#skF_5',k1_tarski('#skF_7'),D_258),k1_tarski('#skF_7'))
      | r2_hidden(D_258,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_258,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1315,c_1461])).

tff(c_1470,plain,(
    ! [D_258] :
      ( r2_hidden('#skF_4'(D_258,'#skF_5',k1_tarski('#skF_7'),D_258),k1_tarski('#skF_7'))
      | r2_hidden(D_258,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_258,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1463])).

tff(c_1477,plain,(
    ! [D_261] :
      ( r2_hidden('#skF_4'(D_261,'#skF_5',k1_tarski('#skF_7'),D_261),k1_tarski('#skF_7'))
      | r2_hidden(D_261,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_261,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1470])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1482,plain,(
    ! [D_262] :
      ( '#skF_4'(D_262,'#skF_5',k1_tarski('#skF_7'),D_262) = '#skF_7'
      | r2_hidden(D_262,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_262,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1477,c_2])).

tff(c_1496,plain,
    ( '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1482,c_1375])).

tff(c_1513,plain,(
    '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1496])).

tff(c_1729,plain,(
    ! [B_274,D_275,C_276] :
      ( ~ r2_orders_2(B_274,D_275,'#skF_4'(D_275,B_274,C_276,D_275))
      | r2_hidden(D_275,a_2_1_orders_2(B_274,C_276))
      | ~ m1_subset_1(D_275,u1_struct_0(B_274))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(u1_struct_0(B_274)))
      | ~ l1_orders_2(B_274)
      | ~ v5_orders_2(B_274)
      | ~ v4_orders_2(B_274)
      | ~ v3_orders_2(B_274)
      | v2_struct_0(B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1739,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_1729])).

tff(c_1757,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1315,c_42,c_1051,c_1739])).

tff(c_1759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1375,c_1757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:25:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.63  
% 4.01/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.64  %$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.01/1.64  
% 4.01/1.64  %Foreground sorts:
% 4.01/1.64  
% 4.01/1.64  
% 4.01/1.64  %Background operators:
% 4.01/1.64  
% 4.01/1.64  
% 4.01/1.64  %Foreground operators:
% 4.01/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.01/1.64  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.01/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.01/1.64  tff('#skF_7', type, '#skF_7': $i).
% 4.01/1.64  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.01/1.64  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 4.01/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.01/1.64  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 4.01/1.64  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.64  tff('#skF_6', type, '#skF_6': $i).
% 4.01/1.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.01/1.64  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.01/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.01/1.64  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.01/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.01/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.01/1.64  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.01/1.64  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 4.01/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.01/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.01/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.64  
% 4.01/1.66  tff(f_144, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_orders_2)).
% 4.01/1.66  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.01/1.66  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 4.01/1.66  tff(f_84, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 4.01/1.66  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.01/1.66  tff(f_57, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 4.01/1.66  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.01/1.66  tff(f_122, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 4.01/1.66  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_50, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_48, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_46, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_44, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_40, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_1060, plain, (![A_162, B_163]: (k6_domain_1(A_162, B_163)=k1_tarski(B_163) | ~m1_subset_1(B_163, A_162) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.01/1.66  tff(c_1067, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_1060])).
% 4.01/1.66  tff(c_1069, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1067])).
% 4.01/1.66  tff(c_34, plain, (![A_28, B_30]: (m1_subset_1(k6_domain_1(u1_struct_0(A_28), B_30), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_30, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | ~v3_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.66  tff(c_1189, plain, (![D_200, B_201, C_202]: (r2_hidden('#skF_4'(D_200, B_201, C_202, D_200), C_202) | r2_hidden(D_200, a_2_1_orders_2(B_201, C_202)) | ~m1_subset_1(D_200, u1_struct_0(B_201)) | ~m1_subset_1(C_202, k1_zfmisc_1(u1_struct_0(B_201))) | ~l1_orders_2(B_201) | ~v5_orders_2(B_201) | ~v4_orders_2(B_201) | ~v3_orders_2(B_201) | v2_struct_0(B_201))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_1208, plain, (![D_218, A_219, B_220]: (r2_hidden('#skF_4'(D_218, A_219, k6_domain_1(u1_struct_0(A_219), B_220), D_218), k6_domain_1(u1_struct_0(A_219), B_220)) | r2_hidden(D_218, a_2_1_orders_2(A_219, k6_domain_1(u1_struct_0(A_219), B_220))) | ~m1_subset_1(D_218, u1_struct_0(A_219)) | ~v5_orders_2(A_219) | ~v4_orders_2(A_219) | ~m1_subset_1(B_220, u1_struct_0(A_219)) | ~l1_orders_2(A_219) | ~v3_orders_2(A_219) | v2_struct_0(A_219))), inference(resolution, [status(thm)], [c_34, c_1189])).
% 4.01/1.66  tff(c_1110, plain, (![A_178, B_179]: (m1_subset_1(k6_domain_1(u1_struct_0(A_178), B_179), k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v3_orders_2(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.66  tff(c_16, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.01/1.66  tff(c_1117, plain, (![A_178, A_7, B_179]: (~v1_xboole_0(u1_struct_0(A_178)) | ~r2_hidden(A_7, k6_domain_1(u1_struct_0(A_178), B_179)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v3_orders_2(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_1110, c_16])).
% 4.01/1.66  tff(c_1213, plain, (![A_221, D_222, B_223]: (~v1_xboole_0(u1_struct_0(A_221)) | r2_hidden(D_222, a_2_1_orders_2(A_221, k6_domain_1(u1_struct_0(A_221), B_223))) | ~m1_subset_1(D_222, u1_struct_0(A_221)) | ~v5_orders_2(A_221) | ~v4_orders_2(A_221) | ~m1_subset_1(B_223, u1_struct_0(A_221)) | ~l1_orders_2(A_221) | ~v3_orders_2(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_1208, c_1117])).
% 4.01/1.66  tff(c_1118, plain, (![A_180, B_181]: (k2_orders_2(A_180, B_181)=a_2_1_orders_2(A_180, B_181) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_orders_2(A_180) | ~v5_orders_2(A_180) | ~v4_orders_2(A_180) | ~v3_orders_2(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.66  tff(c_1149, plain, (![A_193, B_194]: (k2_orders_2(A_193, k6_domain_1(u1_struct_0(A_193), B_194))=a_2_1_orders_2(A_193, k6_domain_1(u1_struct_0(A_193), B_194)) | ~v5_orders_2(A_193) | ~v4_orders_2(A_193) | ~m1_subset_1(B_194, u1_struct_0(A_193)) | ~l1_orders_2(A_193) | ~v3_orders_2(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_34, c_1118])).
% 4.01/1.66  tff(c_54, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_71, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 4.01/1.66  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.66  tff(c_79, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.01/1.66  tff(c_86, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_79])).
% 4.01/1.66  tff(c_88, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_86])).
% 4.01/1.66  tff(c_149, plain, (![A_66, B_67]: (k2_orders_2(A_66, B_67)=a_2_1_orders_2(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.66  tff(c_164, plain, (![A_73, B_74]: (k2_orders_2(A_73, k6_domain_1(u1_struct_0(A_73), B_74))=a_2_1_orders_2(A_73, k6_domain_1(u1_struct_0(A_73), B_74)) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_34, c_149])).
% 4.01/1.66  tff(c_60, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.01/1.66  tff(c_92, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_71, c_60])).
% 4.01/1.66  tff(c_173, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_164, c_92])).
% 4.01/1.66  tff(c_179, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_48, c_46, c_173])).
% 4.01/1.66  tff(c_180, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_52, c_179])).
% 4.01/1.66  tff(c_28, plain, (![A_13, B_14, C_15]: ('#skF_3'(A_13, B_14, C_15)=A_13 | ~r2_hidden(A_13, a_2_1_orders_2(B_14, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(B_14))) | ~l1_orders_2(B_14) | ~v5_orders_2(B_14) | ~v4_orders_2(B_14) | ~v3_orders_2(B_14) | v2_struct_0(B_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_183, plain, ('#skF_3'('#skF_6', '#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))='#skF_6' | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_180, c_28])).
% 4.01/1.66  tff(c_186, plain, ('#skF_3'('#skF_6', '#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))='#skF_6' | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_183])).
% 4.01/1.66  tff(c_187, plain, ('#skF_3'('#skF_6', '#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))='#skF_6' | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_186])).
% 4.01/1.66  tff(c_188, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_187])).
% 4.01/1.66  tff(c_191, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_188])).
% 4.01/1.66  tff(c_194, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_191])).
% 4.01/1.66  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_194])).
% 4.01/1.66  tff(c_198, plain, (m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_187])).
% 4.01/1.66  tff(c_206, plain, (![A_7]: (~v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden(A_7, k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(resolution, [status(thm)], [c_198, c_16])).
% 4.01/1.66  tff(c_214, plain, (![A_7]: (~r2_hidden(A_7, k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_206])).
% 4.01/1.66  tff(c_318, plain, (![D_85, B_86, C_87]: (r2_hidden('#skF_4'(D_85, B_86, C_87, D_85), C_87) | r2_hidden(D_85, a_2_1_orders_2(B_86, C_87)) | ~m1_subset_1(D_85, u1_struct_0(B_86)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(B_86))) | ~l1_orders_2(B_86) | ~v5_orders_2(B_86) | ~v4_orders_2(B_86) | ~v3_orders_2(B_86) | v2_struct_0(B_86))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_320, plain, (![D_85]: (r2_hidden('#skF_4'(D_85, '#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'), D_85), k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')) | r2_hidden(D_85, a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~m1_subset_1(D_85, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_198, c_318])).
% 4.01/1.66  tff(c_325, plain, (![D_85]: (r2_hidden('#skF_4'(D_85, '#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'), D_85), k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')) | r2_hidden(D_85, a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~m1_subset_1(D_85, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_320])).
% 4.01/1.66  tff(c_328, plain, (![D_88]: (r2_hidden(D_88, a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~m1_subset_1(D_88, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_214, c_325])).
% 4.01/1.66  tff(c_18, plain, (![A_10, B_12]: (k2_orders_2(A_10, B_12)=a_2_1_orders_2(A_10, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_orders_2(A_10) | ~v5_orders_2(A_10) | ~v4_orders_2(A_10) | ~v3_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.66  tff(c_201, plain, (k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))=a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_198, c_18])).
% 4.01/1.66  tff(c_209, plain, (k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))=a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_201])).
% 4.01/1.66  tff(c_210, plain, (k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))=a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_209])).
% 4.01/1.66  tff(c_38, plain, (![B_33, A_31]: (~r2_hidden(B_33, k2_orders_2(A_31, k6_domain_1(u1_struct_0(A_31), B_33))) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.01/1.66  tff(c_249, plain, (~r2_hidden('#skF_7', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_210, c_38])).
% 4.01/1.66  tff(c_260, plain, (~r2_hidden('#skF_7', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_40, c_249])).
% 4.01/1.66  tff(c_261, plain, (~r2_hidden('#skF_7', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_52, c_260])).
% 4.01/1.66  tff(c_331, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_328, c_261])).
% 4.01/1.66  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_331])).
% 4.01/1.66  tff(c_342, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 4.01/1.66  tff(c_405, plain, (![A_101, B_102]: (m1_subset_1(k6_domain_1(u1_struct_0(A_101), B_102), k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.66  tff(c_416, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_342, c_405])).
% 4.01/1.66  tff(c_423, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_416])).
% 4.01/1.66  tff(c_424, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_423])).
% 4.01/1.66  tff(c_441, plain, (![A_103, B_104]: (k2_orders_2(A_103, B_104)=a_2_1_orders_2(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.66  tff(c_444, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_424, c_441])).
% 4.01/1.66  tff(c_453, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_444])).
% 4.01/1.66  tff(c_454, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_453])).
% 4.01/1.66  tff(c_348, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_60])).
% 4.01/1.66  tff(c_349, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_71, c_348])).
% 4.01/1.66  tff(c_460, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_349])).
% 4.01/1.66  tff(c_506, plain, (![A_112, B_113, C_114]: ('#skF_3'(A_112, B_113, C_114)=A_112 | ~r2_hidden(A_112, a_2_1_orders_2(B_113, C_114)) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(B_113))) | ~l1_orders_2(B_113) | ~v5_orders_2(B_113) | ~v4_orders_2(B_113) | ~v3_orders_2(B_113) | v2_struct_0(B_113))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_508, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_460, c_506])).
% 4.01/1.66  tff(c_517, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_424, c_508])).
% 4.01/1.66  tff(c_518, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_517])).
% 4.01/1.66  tff(c_991, plain, (![B_150, A_151, C_152, E_153]: (r2_orders_2(B_150, '#skF_3'(A_151, B_150, C_152), E_153) | ~r2_hidden(E_153, C_152) | ~m1_subset_1(E_153, u1_struct_0(B_150)) | ~r2_hidden(A_151, a_2_1_orders_2(B_150, C_152)) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(B_150))) | ~l1_orders_2(B_150) | ~v5_orders_2(B_150) | ~v4_orders_2(B_150) | ~v3_orders_2(B_150) | v2_struct_0(B_150))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_993, plain, (![A_151, E_153]: (r2_orders_2('#skF_5', '#skF_3'(A_151, '#skF_5', k1_tarski('#skF_7')), E_153) | ~r2_hidden(E_153, k1_tarski('#skF_7')) | ~m1_subset_1(E_153, u1_struct_0('#skF_5')) | ~r2_hidden(A_151, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_424, c_991])).
% 4.01/1.66  tff(c_1000, plain, (![A_151, E_153]: (r2_orders_2('#skF_5', '#skF_3'(A_151, '#skF_5', k1_tarski('#skF_7')), E_153) | ~r2_hidden(E_153, k1_tarski('#skF_7')) | ~m1_subset_1(E_153, u1_struct_0('#skF_5')) | ~r2_hidden(A_151, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_993])).
% 4.01/1.66  tff(c_1007, plain, (![A_154, E_155]: (r2_orders_2('#skF_5', '#skF_3'(A_154, '#skF_5', k1_tarski('#skF_7')), E_155) | ~r2_hidden(E_155, k1_tarski('#skF_7')) | ~m1_subset_1(E_155, u1_struct_0('#skF_5')) | ~r2_hidden(A_154, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_1000])).
% 4.01/1.66  tff(c_1019, plain, (![E_155]: (r2_orders_2('#skF_5', '#skF_6', E_155) | ~r2_hidden(E_155, k1_tarski('#skF_7')) | ~m1_subset_1(E_155, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_518, c_1007])).
% 4.01/1.66  tff(c_1026, plain, (![E_156]: (r2_orders_2('#skF_5', '#skF_6', E_156) | ~r2_hidden(E_156, k1_tarski('#skF_7')) | ~m1_subset_1(E_156, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_1019])).
% 4.01/1.66  tff(c_1041, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_1026])).
% 4.01/1.66  tff(c_1047, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1041])).
% 4.01/1.66  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_1047])).
% 4.01/1.66  tff(c_1050, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(splitRight, [status(thm)], [c_54])).
% 4.01/1.66  tff(c_1158, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1149, c_1050])).
% 4.01/1.66  tff(c_1164, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_48, c_46, c_1158])).
% 4.01/1.66  tff(c_1165, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1164])).
% 4.01/1.66  tff(c_1220, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1213, c_1165])).
% 4.01/1.66  tff(c_1230, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_48, c_46, c_42, c_1069, c_1220])).
% 4.01/1.66  tff(c_1232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1230])).
% 4.01/1.66  tff(c_1233, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_1067])).
% 4.01/1.66  tff(c_1296, plain, (![A_238, B_239]: (m1_subset_1(k6_domain_1(u1_struct_0(A_238), B_239), k1_zfmisc_1(u1_struct_0(A_238))) | ~m1_subset_1(B_239, u1_struct_0(A_238)) | ~l1_orders_2(A_238) | ~v3_orders_2(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.66  tff(c_1307, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1233, c_1296])).
% 4.01/1.66  tff(c_1314, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_1307])).
% 4.01/1.66  tff(c_1315, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1314])).
% 4.01/1.66  tff(c_1356, plain, (![A_243, B_244]: (k2_orders_2(A_243, B_244)=a_2_1_orders_2(A_243, B_244) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_orders_2(A_243) | ~v5_orders_2(A_243) | ~v4_orders_2(A_243) | ~v3_orders_2(A_243) | v2_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.66  tff(c_1359, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1315, c_1356])).
% 4.01/1.66  tff(c_1368, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1359])).
% 4.01/1.66  tff(c_1369, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1368])).
% 4.01/1.66  tff(c_1235, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_1050])).
% 4.01/1.66  tff(c_1375, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1235])).
% 4.01/1.66  tff(c_1051, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 4.01/1.66  tff(c_1461, plain, (![D_258, B_259, C_260]: (r2_hidden('#skF_4'(D_258, B_259, C_260, D_258), C_260) | r2_hidden(D_258, a_2_1_orders_2(B_259, C_260)) | ~m1_subset_1(D_258, u1_struct_0(B_259)) | ~m1_subset_1(C_260, k1_zfmisc_1(u1_struct_0(B_259))) | ~l1_orders_2(B_259) | ~v5_orders_2(B_259) | ~v4_orders_2(B_259) | ~v3_orders_2(B_259) | v2_struct_0(B_259))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_1463, plain, (![D_258]: (r2_hidden('#skF_4'(D_258, '#skF_5', k1_tarski('#skF_7'), D_258), k1_tarski('#skF_7')) | r2_hidden(D_258, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_258, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1315, c_1461])).
% 4.01/1.66  tff(c_1470, plain, (![D_258]: (r2_hidden('#skF_4'(D_258, '#skF_5', k1_tarski('#skF_7'), D_258), k1_tarski('#skF_7')) | r2_hidden(D_258, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_258, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1463])).
% 4.01/1.66  tff(c_1477, plain, (![D_261]: (r2_hidden('#skF_4'(D_261, '#skF_5', k1_tarski('#skF_7'), D_261), k1_tarski('#skF_7')) | r2_hidden(D_261, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_261, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1470])).
% 4.01/1.66  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.66  tff(c_1482, plain, (![D_262]: ('#skF_4'(D_262, '#skF_5', k1_tarski('#skF_7'), D_262)='#skF_7' | r2_hidden(D_262, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_262, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1477, c_2])).
% 4.01/1.66  tff(c_1496, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1482, c_1375])).
% 4.01/1.66  tff(c_1513, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1496])).
% 4.01/1.66  tff(c_1729, plain, (![B_274, D_275, C_276]: (~r2_orders_2(B_274, D_275, '#skF_4'(D_275, B_274, C_276, D_275)) | r2_hidden(D_275, a_2_1_orders_2(B_274, C_276)) | ~m1_subset_1(D_275, u1_struct_0(B_274)) | ~m1_subset_1(C_276, k1_zfmisc_1(u1_struct_0(B_274))) | ~l1_orders_2(B_274) | ~v5_orders_2(B_274) | ~v4_orders_2(B_274) | ~v3_orders_2(B_274) | v2_struct_0(B_274))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_1739, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1513, c_1729])).
% 4.01/1.66  tff(c_1757, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1315, c_42, c_1051, c_1739])).
% 4.01/1.66  tff(c_1759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1375, c_1757])).
% 4.01/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.66  
% 4.01/1.66  Inference rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Ref     : 0
% 4.01/1.66  #Sup     : 336
% 4.01/1.66  #Fact    : 0
% 4.01/1.66  #Define  : 0
% 4.01/1.66  #Split   : 11
% 4.01/1.66  #Chain   : 0
% 4.01/1.66  #Close   : 0
% 4.01/1.66  
% 4.01/1.66  Ordering : KBO
% 4.01/1.66  
% 4.01/1.66  Simplification rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Subsume      : 30
% 4.01/1.66  #Demod        : 530
% 4.01/1.66  #Tautology    : 157
% 4.01/1.66  #SimpNegUnit  : 108
% 4.01/1.66  #BackRed      : 5
% 4.01/1.66  
% 4.01/1.66  #Partial instantiations: 0
% 4.01/1.66  #Strategies tried      : 1
% 4.01/1.66  
% 4.01/1.66  Timing (in seconds)
% 4.01/1.66  ----------------------
% 4.01/1.66  Preprocessing        : 0.32
% 4.01/1.66  Parsing              : 0.16
% 4.01/1.66  CNF conversion       : 0.02
% 4.01/1.66  Main loop            : 0.57
% 4.01/1.66  Inferencing          : 0.22
% 4.01/1.66  Reduction            : 0.18
% 4.01/1.66  Demodulation         : 0.13
% 4.01/1.66  BG Simplification    : 0.03
% 4.01/1.66  Subsumption          : 0.09
% 4.01/1.67  Abstraction          : 0.04
% 4.01/1.67  MUC search           : 0.00
% 4.01/1.67  Cooper               : 0.00
% 4.01/1.67  Total                : 0.94
% 4.01/1.67  Index Insertion      : 0.00
% 4.01/1.67  Index Deletion       : 0.00
% 4.01/1.67  Index Matching       : 0.00
% 4.01/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
