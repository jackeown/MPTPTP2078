%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:57 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 374 expanded)
%              Number of leaves         :   53 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 760 expanded)
%              Number of equality atoms :   57 ( 160 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_46,plain,(
    ! [A_49,B_50] : v1_relat_1(k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_201,plain,(
    ! [B_104,A_105] :
      ( v1_relat_1(B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_105))
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_207,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_201])).

tff(c_214,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_207])).

tff(c_64,plain,(
    ! [B_62,A_61] :
      ( r1_tarski(k7_relat_1(B_62,A_61),B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_273,plain,(
    ! [A_111,B_112] :
      ( v1_relat_1(A_111)
      | ~ v1_relat_1(B_112)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_34,c_201])).

tff(c_286,plain,(
    ! [B_62,A_61] :
      ( v1_relat_1(k7_relat_1(B_62,A_61))
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_64,c_273])).

tff(c_48,plain,(
    ! [B_52,A_51] :
      ( k2_relat_1(k7_relat_1(B_52,A_51)) = k9_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1273,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(k2_relat_1(A_233),k2_relat_1(B_234))
      | ~ r1_tarski(A_233,B_234)
      | ~ v1_relat_1(B_234)
      | ~ v1_relat_1(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7364,plain,(
    ! [B_589,A_590,B_591] :
      ( r1_tarski(k9_relat_1(B_589,A_590),k2_relat_1(B_591))
      | ~ r1_tarski(k7_relat_1(B_589,A_590),B_591)
      | ~ v1_relat_1(B_591)
      | ~ v1_relat_1(k7_relat_1(B_589,A_590))
      | ~ v1_relat_1(B_589) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1273])).

tff(c_60,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_222,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_214,c_60])).

tff(c_241,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_422,plain,(
    ! [C_139,A_140,B_141] :
      ( v4_relat_1(C_139,A_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_435,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_422])).

tff(c_54,plain,(
    ! [B_56,A_55] :
      ( k7_relat_1(B_56,A_55) = B_56
      | ~ v4_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_467,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_435,c_54])).

tff(c_470,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_467])).

tff(c_474,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_48])).

tff(c_484,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_474])).

tff(c_40,plain,(
    ! [A_44,B_46] :
      ( k9_relat_1(A_44,k1_tarski(B_46)) = k11_relat_1(A_44,B_46)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_503,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_40])).

tff(c_510,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_503])).

tff(c_50,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,k1_relat_1(B_54))
      | k11_relat_1(B_54,A_53) = k1_xboole_0
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1611,plain,(
    ! [B_265,A_266] :
      ( k1_tarski(k1_funct_1(B_265,A_266)) = k2_relat_1(B_265)
      | k1_tarski(A_266) != k1_relat_1(B_265)
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1475,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( k7_relset_1(A_250,B_251,C_252,D_253) = k9_relat_1(C_252,D_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1487,plain,(
    ! [D_253] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_253) = k9_relat_1('#skF_4',D_253) ),
    inference(resolution,[status(thm)],[c_78,c_1475])).

tff(c_74,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1497,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_74])).

tff(c_1620,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_1497])).

tff(c_1641,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_82,c_1620])).

tff(c_1653,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1641])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1082,plain,(
    ! [A_199,B_200,C_201] :
      ( r1_tarski(k2_tarski(A_199,B_200),C_201)
      | ~ r2_hidden(B_200,C_201)
      | ~ r2_hidden(A_199,C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1108,plain,(
    ! [A_4,C_201] :
      ( r1_tarski(k1_tarski(A_4),C_201)
      | ~ r2_hidden(A_4,C_201)
      | ~ r2_hidden(A_4,C_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1082])).

tff(c_333,plain,(
    ! [B_123,A_124] :
      ( r1_tarski(k1_relat_1(B_123),A_124)
      | ~ v4_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1882,plain,(
    ! [B_310,A_311] :
      ( k1_relat_1(B_310) = A_311
      | ~ r1_tarski(A_311,k1_relat_1(B_310))
      | ~ v4_relat_1(B_310,A_311)
      | ~ v1_relat_1(B_310) ) ),
    inference(resolution,[status(thm)],[c_333,c_2])).

tff(c_4933,plain,(
    ! [A_457,B_458] :
      ( k1_tarski(A_457) = k1_relat_1(B_458)
      | ~ v4_relat_1(B_458,k1_tarski(A_457))
      | ~ v1_relat_1(B_458)
      | ~ r2_hidden(A_457,k1_relat_1(B_458)) ) ),
    inference(resolution,[status(thm)],[c_1108,c_1882])).

tff(c_4959,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_435,c_4933])).

tff(c_4973,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_4959])).

tff(c_4974,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1653,c_4973])).

tff(c_4980,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_4974])).

tff(c_4983,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_510,c_4980])).

tff(c_4985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_4983])).

tff(c_4986,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1641])).

tff(c_7367,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7364,c_4986])).

tff(c_7408,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_7367])).

tff(c_7425,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7408])).

tff(c_7428,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_286,c_7425])).

tff(c_7432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_7428])).

tff(c_7433,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7408])).

tff(c_7445,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_7433])).

tff(c_7449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_7445])).

tff(c_7450,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7457,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7450,c_8])).

tff(c_7451,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_7464,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7450,c_7451])).

tff(c_167,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_7495,plain,(
    ! [A_597] :
      ( A_597 = '#skF_4'
      | ~ r1_tarski(A_597,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7450,c_7450,c_182])).

tff(c_7503,plain,(
    ! [A_61] :
      ( k7_relat_1('#skF_4',A_61) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_7495])).

tff(c_7512,plain,(
    ! [A_61] : k7_relat_1('#skF_4',A_61) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_7503])).

tff(c_7672,plain,(
    ! [B_633,A_634] :
      ( k2_relat_1(k7_relat_1(B_633,A_634)) = k9_relat_1(B_633,A_634)
      | ~ v1_relat_1(B_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7681,plain,(
    ! [A_61] :
      ( k9_relat_1('#skF_4',A_61) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7512,c_7672])).

tff(c_7685,plain,(
    ! [A_61] : k9_relat_1('#skF_4',A_61) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_7464,c_7681])).

tff(c_30,plain,(
    ! [A_35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7456,plain,(
    ! [A_35] : m1_subset_1('#skF_4',k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7450,c_30])).

tff(c_8769,plain,(
    ! [A_740,B_741,C_742,D_743] :
      ( k7_relset_1(A_740,B_741,C_742,D_743) = k9_relat_1(C_742,D_743)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(A_740,B_741))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8774,plain,(
    ! [A_740,B_741,D_743] : k7_relset_1(A_740,B_741,'#skF_4',D_743) = k9_relat_1('#skF_4',D_743) ),
    inference(resolution,[status(thm)],[c_7456,c_8769])).

tff(c_8779,plain,(
    ! [A_740,B_741,D_743] : k7_relset_1(A_740,B_741,'#skF_4',D_743) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7685,c_8774])).

tff(c_8781,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_74])).

tff(c_8784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7457,c_8781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.98/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.47  
% 6.98/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.98/2.47  
% 6.98/2.47  %Foreground sorts:
% 6.98/2.47  
% 6.98/2.47  
% 6.98/2.47  %Background operators:
% 6.98/2.47  
% 6.98/2.47  
% 6.98/2.47  %Foreground operators:
% 6.98/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.98/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.98/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.98/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.98/2.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.98/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.98/2.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.98/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.98/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.98/2.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.98/2.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.98/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.98/2.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.98/2.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 6.98/2.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.98/2.47  tff('#skF_2', type, '#skF_2': $i).
% 6.98/2.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.98/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.98/2.47  tff('#skF_1', type, '#skF_1': $i).
% 6.98/2.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.98/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.98/2.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.98/2.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.98/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.98/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.98/2.47  tff('#skF_4', type, '#skF_4': $i).
% 6.98/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.98/2.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.98/2.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.98/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.98/2.47  
% 6.98/2.49  tff(f_85, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.98/2.49  tff(f_155, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 6.98/2.49  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.98/2.49  tff(f_125, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 6.98/2.49  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.98/2.49  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.98/2.49  tff(f_113, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.98/2.49  tff(f_121, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.98/2.49  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.98/2.49  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.98/2.49  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 6.98/2.49  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 6.98/2.49  tff(f_133, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.98/2.49  tff(f_143, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.98/2.49  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.98/2.49  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.98/2.49  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.98/2.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.98/2.49  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.98/2.49  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.98/2.49  tff(c_46, plain, (![A_49, B_50]: (v1_relat_1(k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.98/2.49  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.98/2.49  tff(c_201, plain, (![B_104, A_105]: (v1_relat_1(B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_105)) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.98/2.49  tff(c_207, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_201])).
% 6.98/2.49  tff(c_214, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_207])).
% 6.98/2.49  tff(c_64, plain, (![B_62, A_61]: (r1_tarski(k7_relat_1(B_62, A_61), B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.98/2.49  tff(c_34, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.98/2.49  tff(c_273, plain, (![A_111, B_112]: (v1_relat_1(A_111) | ~v1_relat_1(B_112) | ~r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_34, c_201])).
% 6.98/2.49  tff(c_286, plain, (![B_62, A_61]: (v1_relat_1(k7_relat_1(B_62, A_61)) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_64, c_273])).
% 6.98/2.49  tff(c_48, plain, (![B_52, A_51]: (k2_relat_1(k7_relat_1(B_52, A_51))=k9_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.98/2.49  tff(c_1273, plain, (![A_233, B_234]: (r1_tarski(k2_relat_1(A_233), k2_relat_1(B_234)) | ~r1_tarski(A_233, B_234) | ~v1_relat_1(B_234) | ~v1_relat_1(A_233))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.98/2.49  tff(c_7364, plain, (![B_589, A_590, B_591]: (r1_tarski(k9_relat_1(B_589, A_590), k2_relat_1(B_591)) | ~r1_tarski(k7_relat_1(B_589, A_590), B_591) | ~v1_relat_1(B_591) | ~v1_relat_1(k7_relat_1(B_589, A_590)) | ~v1_relat_1(B_589))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1273])).
% 6.98/2.49  tff(c_60, plain, (![A_60]: (k2_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.98/2.49  tff(c_222, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_214, c_60])).
% 6.98/2.49  tff(c_241, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_222])).
% 6.98/2.49  tff(c_422, plain, (![C_139, A_140, B_141]: (v4_relat_1(C_139, A_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.98/2.49  tff(c_435, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_422])).
% 6.98/2.49  tff(c_54, plain, (![B_56, A_55]: (k7_relat_1(B_56, A_55)=B_56 | ~v4_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.98/2.49  tff(c_467, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_435, c_54])).
% 6.98/2.49  tff(c_470, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_467])).
% 6.98/2.49  tff(c_474, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_470, c_48])).
% 6.98/2.49  tff(c_484, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_474])).
% 6.98/2.49  tff(c_40, plain, (![A_44, B_46]: (k9_relat_1(A_44, k1_tarski(B_46))=k11_relat_1(A_44, B_46) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.98/2.49  tff(c_503, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_484, c_40])).
% 6.98/2.49  tff(c_510, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_503])).
% 6.98/2.49  tff(c_50, plain, (![A_53, B_54]: (r2_hidden(A_53, k1_relat_1(B_54)) | k11_relat_1(B_54, A_53)=k1_xboole_0 | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.98/2.49  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.98/2.49  tff(c_1611, plain, (![B_265, A_266]: (k1_tarski(k1_funct_1(B_265, A_266))=k2_relat_1(B_265) | k1_tarski(A_266)!=k1_relat_1(B_265) | ~v1_funct_1(B_265) | ~v1_relat_1(B_265))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.98/2.49  tff(c_1475, plain, (![A_250, B_251, C_252, D_253]: (k7_relset_1(A_250, B_251, C_252, D_253)=k9_relat_1(C_252, D_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.98/2.49  tff(c_1487, plain, (![D_253]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_253)=k9_relat_1('#skF_4', D_253))), inference(resolution, [status(thm)], [c_78, c_1475])).
% 6.98/2.49  tff(c_74, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.98/2.49  tff(c_1497, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_74])).
% 6.98/2.49  tff(c_1620, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1611, c_1497])).
% 6.98/2.49  tff(c_1641, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_82, c_1620])).
% 6.98/2.49  tff(c_1653, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1641])).
% 6.98/2.49  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.98/2.49  tff(c_1082, plain, (![A_199, B_200, C_201]: (r1_tarski(k2_tarski(A_199, B_200), C_201) | ~r2_hidden(B_200, C_201) | ~r2_hidden(A_199, C_201))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.98/2.49  tff(c_1108, plain, (![A_4, C_201]: (r1_tarski(k1_tarski(A_4), C_201) | ~r2_hidden(A_4, C_201) | ~r2_hidden(A_4, C_201))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1082])).
% 6.98/2.49  tff(c_333, plain, (![B_123, A_124]: (r1_tarski(k1_relat_1(B_123), A_124) | ~v4_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.98/2.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.98/2.49  tff(c_1882, plain, (![B_310, A_311]: (k1_relat_1(B_310)=A_311 | ~r1_tarski(A_311, k1_relat_1(B_310)) | ~v4_relat_1(B_310, A_311) | ~v1_relat_1(B_310))), inference(resolution, [status(thm)], [c_333, c_2])).
% 6.98/2.49  tff(c_4933, plain, (![A_457, B_458]: (k1_tarski(A_457)=k1_relat_1(B_458) | ~v4_relat_1(B_458, k1_tarski(A_457)) | ~v1_relat_1(B_458) | ~r2_hidden(A_457, k1_relat_1(B_458)))), inference(resolution, [status(thm)], [c_1108, c_1882])).
% 6.98/2.49  tff(c_4959, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_435, c_4933])).
% 6.98/2.49  tff(c_4973, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_4959])).
% 6.98/2.49  tff(c_4974, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1653, c_4973])).
% 6.98/2.49  tff(c_4980, plain, (k11_relat_1('#skF_4', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_4974])).
% 6.98/2.49  tff(c_4983, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_214, c_510, c_4980])).
% 6.98/2.49  tff(c_4985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_4983])).
% 6.98/2.49  tff(c_4986, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1641])).
% 6.98/2.49  tff(c_7367, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_7364, c_4986])).
% 6.98/2.49  tff(c_7408, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_7367])).
% 6.98/2.49  tff(c_7425, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7408])).
% 6.98/2.49  tff(c_7428, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_286, c_7425])).
% 6.98/2.49  tff(c_7432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_7428])).
% 6.98/2.49  tff(c_7433, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_7408])).
% 6.98/2.49  tff(c_7445, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_7433])).
% 6.98/2.49  tff(c_7449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_7445])).
% 6.98/2.49  tff(c_7450, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_222])).
% 6.98/2.49  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.98/2.49  tff(c_7457, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7450, c_8])).
% 6.98/2.49  tff(c_7451, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_222])).
% 6.98/2.49  tff(c_7464, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7450, c_7451])).
% 6.98/2.49  tff(c_167, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.98/2.49  tff(c_182, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_167])).
% 6.98/2.49  tff(c_7495, plain, (![A_597]: (A_597='#skF_4' | ~r1_tarski(A_597, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7450, c_7450, c_182])).
% 6.98/2.49  tff(c_7503, plain, (![A_61]: (k7_relat_1('#skF_4', A_61)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_7495])).
% 6.98/2.49  tff(c_7512, plain, (![A_61]: (k7_relat_1('#skF_4', A_61)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_7503])).
% 6.98/2.49  tff(c_7672, plain, (![B_633, A_634]: (k2_relat_1(k7_relat_1(B_633, A_634))=k9_relat_1(B_633, A_634) | ~v1_relat_1(B_633))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.98/2.49  tff(c_7681, plain, (![A_61]: (k9_relat_1('#skF_4', A_61)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7512, c_7672])).
% 6.98/2.49  tff(c_7685, plain, (![A_61]: (k9_relat_1('#skF_4', A_61)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_7464, c_7681])).
% 6.98/2.49  tff(c_30, plain, (![A_35]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.98/2.49  tff(c_7456, plain, (![A_35]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_7450, c_30])).
% 6.98/2.49  tff(c_8769, plain, (![A_740, B_741, C_742, D_743]: (k7_relset_1(A_740, B_741, C_742, D_743)=k9_relat_1(C_742, D_743) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.98/2.49  tff(c_8774, plain, (![A_740, B_741, D_743]: (k7_relset_1(A_740, B_741, '#skF_4', D_743)=k9_relat_1('#skF_4', D_743))), inference(resolution, [status(thm)], [c_7456, c_8769])).
% 6.98/2.49  tff(c_8779, plain, (![A_740, B_741, D_743]: (k7_relset_1(A_740, B_741, '#skF_4', D_743)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7685, c_8774])).
% 6.98/2.49  tff(c_8781, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_74])).
% 6.98/2.49  tff(c_8784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7457, c_8781])).
% 6.98/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.49  
% 6.98/2.49  Inference rules
% 6.98/2.49  ----------------------
% 6.98/2.49  #Ref     : 0
% 6.98/2.49  #Sup     : 1845
% 6.98/2.49  #Fact    : 0
% 6.98/2.49  #Define  : 0
% 6.98/2.49  #Split   : 11
% 6.98/2.49  #Chain   : 0
% 6.98/2.49  #Close   : 0
% 6.98/2.49  
% 6.98/2.49  Ordering : KBO
% 6.98/2.49  
% 6.98/2.49  Simplification rules
% 6.98/2.49  ----------------------
% 6.98/2.49  #Subsume      : 333
% 6.98/2.49  #Demod        : 1723
% 6.98/2.49  #Tautology    : 802
% 6.98/2.49  #SimpNegUnit  : 48
% 6.98/2.49  #BackRed      : 47
% 6.98/2.49  
% 6.98/2.49  #Partial instantiations: 0
% 6.98/2.49  #Strategies tried      : 1
% 6.98/2.49  
% 6.98/2.49  Timing (in seconds)
% 6.98/2.49  ----------------------
% 6.98/2.49  Preprocessing        : 0.33
% 6.98/2.49  Parsing              : 0.17
% 6.98/2.49  CNF conversion       : 0.02
% 6.98/2.49  Main loop            : 1.39
% 6.98/2.49  Inferencing          : 0.44
% 6.98/2.49  Reduction            : 0.49
% 6.98/2.49  Demodulation         : 0.36
% 6.98/2.49  BG Simplification    : 0.05
% 6.98/2.49  Subsumption          : 0.31
% 6.98/2.49  Abstraction          : 0.05
% 6.98/2.49  MUC search           : 0.00
% 6.98/2.49  Cooper               : 0.00
% 6.98/2.49  Total                : 1.76
% 6.98/2.49  Index Insertion      : 0.00
% 6.98/2.49  Index Deletion       : 0.00
% 6.98/2.49  Index Matching       : 0.00
% 6.98/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
