%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:22 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   69 (  81 expanded)
%              Number of leaves         :   38 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :   95 ( 139 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_36,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_107,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_113,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_107])).

tff(c_117,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_229,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_238,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_229])).

tff(c_960,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_971,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_960])).

tff(c_976,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_238,c_971])).

tff(c_977,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_976])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [D_39,A_40] : r2_hidden(D_39,k2_tarski(A_40,D_39)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_77])).

tff(c_1015,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_80])).

tff(c_195,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_195])).

tff(c_363,plain,(
    ! [A_101,B_102,C_103] :
      ( m1_subset_1(k2_relset_1(A_101,B_102,C_103),k1_zfmisc_1(B_102))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_383,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_363])).

tff(c_389,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_383])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_397,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_389,c_30])).

tff(c_437,plain,(
    ! [B_113,A_114] :
      ( r2_hidden(k1_funct_1(B_113,A_114),k2_relat_1(B_113))
      | ~ r2_hidden(A_114,k1_relat_1(B_113))
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4857,plain,(
    ! [B_14223,A_14224,B_14225] :
      ( r2_hidden(k1_funct_1(B_14223,A_14224),B_14225)
      | ~ r1_tarski(k2_relat_1(B_14223),B_14225)
      | ~ r2_hidden(A_14224,k1_relat_1(B_14223))
      | ~ v1_funct_1(B_14223)
      | ~ v1_relat_1(B_14223) ) ),
    inference(resolution,[status(thm)],[c_437,c_2])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4876,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4857,c_58])).

tff(c_4889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_66,c_1015,c_397,c_4876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.04  
% 5.31/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.04  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.31/2.04  
% 5.31/2.04  %Foreground sorts:
% 5.31/2.04  
% 5.31/2.04  
% 5.31/2.04  %Background operators:
% 5.31/2.04  
% 5.31/2.04  
% 5.31/2.04  %Foreground operators:
% 5.31/2.04  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.31/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.31/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.31/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.31/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.31/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.31/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.31/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.31/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.31/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.31/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.31/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.31/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.31/2.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.31/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.31/2.04  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.31/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.31/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.31/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.31/2.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.31/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.31/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.31/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.31/2.04  
% 5.31/2.05  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.31/2.05  tff(f_108, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 5.31/2.05  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.31/2.05  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.31/2.05  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.31/2.05  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.31/2.05  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.31/2.05  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.31/2.05  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.31/2.05  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.31/2.05  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 5.31/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.31/2.05  tff(c_36, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.31/2.05  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.31/2.05  tff(c_107, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.31/2.05  tff(c_113, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_107])).
% 5.31/2.05  tff(c_117, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113])).
% 5.31/2.05  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.31/2.05  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.31/2.05  tff(c_64, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.31/2.05  tff(c_229, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.31/2.05  tff(c_238, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_229])).
% 5.31/2.05  tff(c_960, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.31/2.05  tff(c_971, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_62, c_960])).
% 5.31/2.05  tff(c_976, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_238, c_971])).
% 5.31/2.05  tff(c_977, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_976])).
% 5.31/2.05  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.31/2.05  tff(c_77, plain, (![D_39, A_40]: (r2_hidden(D_39, k2_tarski(A_40, D_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.31/2.05  tff(c_80, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_77])).
% 5.31/2.05  tff(c_1015, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_977, c_80])).
% 5.31/2.05  tff(c_195, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.31/2.05  tff(c_204, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_195])).
% 5.31/2.05  tff(c_363, plain, (![A_101, B_102, C_103]: (m1_subset_1(k2_relset_1(A_101, B_102, C_103), k1_zfmisc_1(B_102)) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.31/2.05  tff(c_383, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_204, c_363])).
% 5.31/2.05  tff(c_389, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_383])).
% 5.31/2.05  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.31/2.05  tff(c_397, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_389, c_30])).
% 5.31/2.05  tff(c_437, plain, (![B_113, A_114]: (r2_hidden(k1_funct_1(B_113, A_114), k2_relat_1(B_113)) | ~r2_hidden(A_114, k1_relat_1(B_113)) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.31/2.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/2.05  tff(c_4857, plain, (![B_14223, A_14224, B_14225]: (r2_hidden(k1_funct_1(B_14223, A_14224), B_14225) | ~r1_tarski(k2_relat_1(B_14223), B_14225) | ~r2_hidden(A_14224, k1_relat_1(B_14223)) | ~v1_funct_1(B_14223) | ~v1_relat_1(B_14223))), inference(resolution, [status(thm)], [c_437, c_2])).
% 5.31/2.05  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.31/2.05  tff(c_4876, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4857, c_58])).
% 5.31/2.05  tff(c_4889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_66, c_1015, c_397, c_4876])).
% 5.31/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.05  
% 5.31/2.05  Inference rules
% 5.31/2.05  ----------------------
% 5.31/2.05  #Ref     : 0
% 5.31/2.05  #Sup     : 670
% 5.31/2.05  #Fact    : 4
% 5.31/2.05  #Define  : 0
% 5.31/2.05  #Split   : 12
% 5.31/2.05  #Chain   : 0
% 5.31/2.05  #Close   : 0
% 5.31/2.05  
% 5.31/2.05  Ordering : KBO
% 5.31/2.05  
% 5.31/2.05  Simplification rules
% 5.31/2.05  ----------------------
% 5.31/2.05  #Subsume      : 142
% 5.31/2.05  #Demod        : 171
% 5.31/2.05  #Tautology    : 186
% 5.31/2.05  #SimpNegUnit  : 16
% 5.31/2.05  #BackRed      : 8
% 5.31/2.05  
% 5.31/2.05  #Partial instantiations: 7670
% 5.31/2.05  #Strategies tried      : 1
% 5.31/2.05  
% 5.31/2.05  Timing (in seconds)
% 5.31/2.05  ----------------------
% 5.31/2.06  Preprocessing        : 0.35
% 5.31/2.06  Parsing              : 0.18
% 5.31/2.06  CNF conversion       : 0.02
% 5.31/2.06  Main loop            : 0.94
% 5.31/2.06  Inferencing          : 0.47
% 5.31/2.06  Reduction            : 0.23
% 5.31/2.06  Demodulation         : 0.16
% 5.31/2.06  BG Simplification    : 0.04
% 5.31/2.06  Subsumption          : 0.14
% 5.31/2.06  Abstraction          : 0.04
% 5.31/2.06  MUC search           : 0.00
% 5.31/2.06  Cooper               : 0.00
% 5.31/2.06  Total                : 1.32
% 5.31/2.06  Index Insertion      : 0.00
% 5.31/2.06  Index Deletion       : 0.00
% 5.31/2.06  Index Matching       : 0.00
% 5.31/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
