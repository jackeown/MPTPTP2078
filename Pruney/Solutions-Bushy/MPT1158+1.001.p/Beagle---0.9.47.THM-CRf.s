%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1158+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:31 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 411 expanded)
%              Number of leaves         :   34 ( 156 expanded)
%              Depth                    :   18
%              Number of atoms          :  253 (1467 expanded)
%              Number of equality atoms :   27 ( 114 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_40,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_93,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1371,plain,(
    ! [A_134,B_135] :
      ( k6_domain_1(A_134,B_135) = k1_tarski(B_135)
      | ~ m1_subset_1(B_135,A_134)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1378,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_1371])).

tff(c_1380,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1378])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1384,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1380,c_20])).

tff(c_1387,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1384])).

tff(c_1390,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1387])).

tff(c_1394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1390])).

tff(c_1396,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_1395,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_1408,plain,(
    ! [A_142,B_143] :
      ( m1_subset_1(k6_domain_1(A_142,B_143),k1_zfmisc_1(A_142))
      | ~ m1_subset_1(B_143,A_142)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1416,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_1408])).

tff(c_1423,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1416])).

tff(c_1424,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1396,c_1423])).

tff(c_1514,plain,(
    ! [A_157,B_158] :
      ( k2_orders_2(A_157,B_158) = a_2_1_orders_2(A_157,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_orders_2(A_157)
      | ~ v5_orders_2(A_157)
      | ~ v4_orders_2(A_157)
      | ~ v3_orders_2(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1520,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1424,c_1514])).

tff(c_1531,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1520])).

tff(c_1532,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1531])).

tff(c_58,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_61,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_97,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_52])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_77,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_80,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_83,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_20])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_83])).

tff(c_89,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_89])).

tff(c_95,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_94,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_108,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k6_domain_1(A_47,B_48),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_119,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_108])).

tff(c_126,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_119])).

tff(c_127,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_126])).

tff(c_213,plain,(
    ! [A_60,B_61] :
      ( k2_orders_2(A_60,B_61) = a_2_1_orders_2(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_orders_2(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_216,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_213])).

tff(c_226,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_216])).

tff(c_227,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_226])).

tff(c_98,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_61])).

tff(c_233,plain,(
    r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_98])).

tff(c_324,plain,(
    ! [A_70,B_71,C_72] :
      ( '#skF_3'(A_70,B_71,C_72) = A_70
      | ~ r2_hidden(A_70,a_2_1_orders_2(B_71,C_72))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(B_71)))
      | ~ l1_orders_2(B_71)
      | ~ v5_orders_2(B_71)
      | ~ v4_orders_2(B_71)
      | ~ v3_orders_2(B_71)
      | v2_struct_0(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_326,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_233,c_324])).

tff(c_335,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_127,c_326])).

tff(c_336,plain,(
    '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_335])).

tff(c_1290,plain,(
    ! [B_124,A_125,C_126,E_127] :
      ( r2_orders_2(B_124,'#skF_3'(A_125,B_124,C_126),E_127)
      | ~ r2_hidden(E_127,C_126)
      | ~ m1_subset_1(E_127,u1_struct_0(B_124))
      | ~ r2_hidden(A_125,a_2_1_orders_2(B_124,C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(B_124)))
      | ~ l1_orders_2(B_124)
      | ~ v5_orders_2(B_124)
      | ~ v4_orders_2(B_124)
      | ~ v3_orders_2(B_124)
      | v2_struct_0(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1299,plain,(
    ! [A_125,E_127] :
      ( r2_orders_2('#skF_5','#skF_3'(A_125,'#skF_5',k1_tarski('#skF_7')),E_127)
      | ~ r2_hidden(E_127,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_127,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_125,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_127,c_1290])).

tff(c_1316,plain,(
    ! [A_125,E_127] :
      ( r2_orders_2('#skF_5','#skF_3'(A_125,'#skF_5',k1_tarski('#skF_7')),E_127)
      | ~ r2_hidden(E_127,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_127,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_125,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1299])).

tff(c_1323,plain,(
    ! [A_128,E_129] :
      ( r2_orders_2('#skF_5','#skF_3'(A_128,'#skF_5',k1_tarski('#skF_7')),E_129)
      | ~ r2_hidden(E_129,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_129,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_128,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1316])).

tff(c_1329,plain,(
    ! [E_129] :
      ( r2_orders_2('#skF_5','#skF_6',E_129)
      | ~ r2_hidden(E_129,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_129,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1323])).

tff(c_1336,plain,(
    ! [E_130] :
      ( r2_orders_2('#skF_5','#skF_6',E_130)
      | ~ r2_hidden(E_130,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_130,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_1329])).

tff(c_1351,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_1336])).

tff(c_1357,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1351])).

tff(c_1359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_1357])).

tff(c_1360,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1363,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_52])).

tff(c_1402,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1363])).

tff(c_1538,plain,(
    ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1402])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2036,plain,(
    ! [D_198,B_199,C_200] :
      ( r2_hidden('#skF_4'(D_198,B_199,C_200,D_198),C_200)
      | r2_hidden(D_198,a_2_1_orders_2(B_199,C_200))
      | ~ m1_subset_1(D_198,u1_struct_0(B_199))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(u1_struct_0(B_199)))
      | ~ l1_orders_2(B_199)
      | ~ v5_orders_2(B_199)
      | ~ v4_orders_2(B_199)
      | ~ v3_orders_2(B_199)
      | v2_struct_0(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2047,plain,(
    ! [D_198] :
      ( r2_hidden('#skF_4'(D_198,'#skF_5',k1_tarski('#skF_7'),D_198),k1_tarski('#skF_7'))
      | r2_hidden(D_198,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_198,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1424,c_2036])).

tff(c_2066,plain,(
    ! [D_198] :
      ( r2_hidden('#skF_4'(D_198,'#skF_5',k1_tarski('#skF_7'),D_198),k1_tarski('#skF_7'))
      | r2_hidden(D_198,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_198,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_2047])).

tff(c_2149,plain,(
    ! [D_204] :
      ( r2_hidden('#skF_4'(D_204,'#skF_5',k1_tarski('#skF_7'),D_204),k1_tarski('#skF_7'))
      | r2_hidden(D_204,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2066])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2158,plain,(
    ! [D_205] :
      ( '#skF_4'(D_205,'#skF_5',k1_tarski('#skF_7'),D_205) = '#skF_7'
      | r2_hidden(D_205,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_205,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2149,c_4])).

tff(c_2169,plain,
    ( '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2158,c_1538])).

tff(c_2183,plain,(
    '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2169])).

tff(c_2375,plain,(
    ! [B_214,D_215,C_216] :
      ( ~ r2_orders_2(B_214,D_215,'#skF_4'(D_215,B_214,C_216,D_215))
      | r2_hidden(D_215,a_2_1_orders_2(B_214,C_216))
      | ~ m1_subset_1(D_215,u1_struct_0(B_214))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(B_214)))
      | ~ l1_orders_2(B_214)
      | ~ v5_orders_2(B_214)
      | ~ v4_orders_2(B_214)
      | ~ v3_orders_2(B_214)
      | v2_struct_0(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2379,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2183,c_2375])).

tff(c_2392,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1424,c_40,c_1360,c_2379])).

tff(c_2394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1538,c_2392])).

%------------------------------------------------------------------------------
