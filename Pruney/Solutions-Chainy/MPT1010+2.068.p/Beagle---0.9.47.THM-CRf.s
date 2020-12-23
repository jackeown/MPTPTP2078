%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:14 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 115 expanded)
%              Number of leaves         :   45 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 209 expanded)
%              Number of equality atoms :   38 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_74,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_785,plain,(
    ! [A_197,B_198,C_199] :
      ( k1_relset_1(A_197,B_198,C_199) = k1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_789,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_785])).

tff(c_1185,plain,(
    ! [B_261,A_262,C_263] :
      ( k1_xboole_0 = B_261
      | k1_relset_1(A_262,B_261,C_263) = A_262
      | ~ v1_funct_2(C_263,A_262,B_261)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1192,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_1185])).

tff(c_1196,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_789,c_1192])).

tff(c_1197,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1196])).

tff(c_142,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_146,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_142])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_850,plain,(
    ! [A_213,D_214] :
      ( r2_hidden(k1_funct_1(A_213,D_214),k2_relat_1(A_213))
      | ~ r2_hidden(D_214,k1_relat_1(A_213))
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_790,plain,(
    ! [A_200,B_201,C_202] :
      ( k2_relset_1(A_200,B_201,C_202) = k2_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_794,plain,(
    k2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_790])).

tff(c_804,plain,(
    ! [A_204,B_205,C_206] :
      ( m1_subset_1(k2_relset_1(A_204,B_205,C_206),k1_zfmisc_1(B_205))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_821,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_804])).

tff(c_827,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_821])).

tff(c_30,plain,(
    ! [A_14,C_16,B_15] :
      ( m1_subset_1(A_14,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_830,plain,(
    ! [A_14] :
      ( m1_subset_1(A_14,k1_tarski('#skF_8'))
      | ~ r2_hidden(A_14,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_827,c_30])).

tff(c_854,plain,(
    ! [D_214] :
      ( m1_subset_1(k1_funct_1('#skF_10',D_214),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_214,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_850,c_830])).

tff(c_862,plain,(
    ! [D_215] :
      ( m1_subset_1(k1_funct_1('#skF_10',D_215),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_215,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_80,c_854])).

tff(c_26,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_747,plain,(
    ! [D_186,B_187,A_188] :
      ( D_186 = B_187
      | D_186 = A_188
      | ~ r2_hidden(D_186,k2_tarski(A_188,B_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_766,plain,(
    ! [D_189,A_190] :
      ( D_189 = A_190
      | D_189 = A_190
      | ~ r2_hidden(D_189,k1_tarski(A_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_747])).

tff(c_770,plain,(
    ! [A_190,A_12] :
      ( A_190 = A_12
      | v1_xboole_0(k1_tarski(A_190))
      | ~ m1_subset_1(A_12,k1_tarski(A_190)) ) ),
    inference(resolution,[status(thm)],[c_28,c_766])).

tff(c_776,plain,(
    ! [A_190,A_12] :
      ( A_190 = A_12
      | ~ m1_subset_1(A_12,k1_tarski(A_190)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_770])).

tff(c_866,plain,(
    ! [D_215] :
      ( k1_funct_1('#skF_10',D_215) = '#skF_8'
      | ~ r2_hidden(D_215,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_862,c_776])).

tff(c_1220,plain,(
    ! [D_264] :
      ( k1_funct_1('#skF_10',D_264) = '#skF_8'
      | ~ r2_hidden(D_264,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_866])).

tff(c_1227,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_74,c_1220])).

tff(c_1233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1227])).

tff(c_1234,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_92,plain,(
    ! [D_77,A_78] : r2_hidden(D_77,k2_tarski(A_78,D_77)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_95,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_92])).

tff(c_102,plain,(
    ! [B_82,A_83] :
      ( ~ r1_tarski(B_82,A_83)
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,(
    ! [A_8] : ~ r1_tarski(k1_tarski(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_95,c_102])).

tff(c_1254,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1234,c_116])).

tff(c_1264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.87  
% 4.06/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.88  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 4.06/1.88  
% 4.06/1.88  %Foreground sorts:
% 4.06/1.88  
% 4.06/1.88  
% 4.06/1.88  %Background operators:
% 4.06/1.88  
% 4.06/1.88  
% 4.06/1.88  %Foreground operators:
% 4.06/1.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.06/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.06/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.06/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.88  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.06/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.06/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.06/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.06/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.88  tff('#skF_10', type, '#skF_10': $i).
% 4.06/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.06/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.06/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.06/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.06/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.06/1.88  tff('#skF_9', type, '#skF_9': $i).
% 4.06/1.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.06/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.06/1.88  tff('#skF_8', type, '#skF_8': $i).
% 4.06/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.06/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.06/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.06/1.88  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.06/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.06/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.06/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.88  
% 4.06/1.90  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.06/1.90  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.06/1.90  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.06/1.90  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.06/1.90  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.06/1.90  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.06/1.90  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.06/1.90  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.06/1.90  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.06/1.90  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.06/1.90  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.06/1.90  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.06/1.90  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.06/1.90  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.06/1.90  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.06/1.90  tff(c_72, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.90  tff(c_74, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.90  tff(c_78, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.90  tff(c_76, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.90  tff(c_785, plain, (![A_197, B_198, C_199]: (k1_relset_1(A_197, B_198, C_199)=k1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.06/1.90  tff(c_789, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_785])).
% 4.06/1.90  tff(c_1185, plain, (![B_261, A_262, C_263]: (k1_xboole_0=B_261 | k1_relset_1(A_262, B_261, C_263)=A_262 | ~v1_funct_2(C_263, A_262, B_261) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.06/1.90  tff(c_1192, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_76, c_1185])).
% 4.06/1.90  tff(c_1196, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_789, c_1192])).
% 4.06/1.90  tff(c_1197, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1196])).
% 4.06/1.90  tff(c_142, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.06/1.90  tff(c_146, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_142])).
% 4.06/1.90  tff(c_80, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.90  tff(c_850, plain, (![A_213, D_214]: (r2_hidden(k1_funct_1(A_213, D_214), k2_relat_1(A_213)) | ~r2_hidden(D_214, k1_relat_1(A_213)) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.06/1.90  tff(c_790, plain, (![A_200, B_201, C_202]: (k2_relset_1(A_200, B_201, C_202)=k2_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.06/1.90  tff(c_794, plain, (k2_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_790])).
% 4.06/1.90  tff(c_804, plain, (![A_204, B_205, C_206]: (m1_subset_1(k2_relset_1(A_204, B_205, C_206), k1_zfmisc_1(B_205)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.06/1.90  tff(c_821, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_794, c_804])).
% 4.06/1.90  tff(c_827, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_821])).
% 4.06/1.90  tff(c_30, plain, (![A_14, C_16, B_15]: (m1_subset_1(A_14, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.06/1.90  tff(c_830, plain, (![A_14]: (m1_subset_1(A_14, k1_tarski('#skF_8')) | ~r2_hidden(A_14, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_827, c_30])).
% 4.06/1.90  tff(c_854, plain, (![D_214]: (m1_subset_1(k1_funct_1('#skF_10', D_214), k1_tarski('#skF_8')) | ~r2_hidden(D_214, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_850, c_830])).
% 4.06/1.90  tff(c_862, plain, (![D_215]: (m1_subset_1(k1_funct_1('#skF_10', D_215), k1_tarski('#skF_8')) | ~r2_hidden(D_215, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_80, c_854])).
% 4.06/1.90  tff(c_26, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.06/1.90  tff(c_28, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.90  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.06/1.90  tff(c_747, plain, (![D_186, B_187, A_188]: (D_186=B_187 | D_186=A_188 | ~r2_hidden(D_186, k2_tarski(A_188, B_187)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.06/1.90  tff(c_766, plain, (![D_189, A_190]: (D_189=A_190 | D_189=A_190 | ~r2_hidden(D_189, k1_tarski(A_190)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_747])).
% 4.06/1.90  tff(c_770, plain, (![A_190, A_12]: (A_190=A_12 | v1_xboole_0(k1_tarski(A_190)) | ~m1_subset_1(A_12, k1_tarski(A_190)))), inference(resolution, [status(thm)], [c_28, c_766])).
% 4.06/1.90  tff(c_776, plain, (![A_190, A_12]: (A_190=A_12 | ~m1_subset_1(A_12, k1_tarski(A_190)))), inference(negUnitSimplification, [status(thm)], [c_26, c_770])).
% 4.06/1.90  tff(c_866, plain, (![D_215]: (k1_funct_1('#skF_10', D_215)='#skF_8' | ~r2_hidden(D_215, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_862, c_776])).
% 4.06/1.90  tff(c_1220, plain, (![D_264]: (k1_funct_1('#skF_10', D_264)='#skF_8' | ~r2_hidden(D_264, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_866])).
% 4.06/1.90  tff(c_1227, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_74, c_1220])).
% 4.06/1.90  tff(c_1233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1227])).
% 4.06/1.90  tff(c_1234, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1196])).
% 4.06/1.90  tff(c_92, plain, (![D_77, A_78]: (r2_hidden(D_77, k2_tarski(A_78, D_77)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.06/1.90  tff(c_95, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_92])).
% 4.06/1.90  tff(c_102, plain, (![B_82, A_83]: (~r1_tarski(B_82, A_83) | ~r2_hidden(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.06/1.90  tff(c_116, plain, (![A_8]: (~r1_tarski(k1_tarski(A_8), A_8))), inference(resolution, [status(thm)], [c_95, c_102])).
% 4.06/1.90  tff(c_1254, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1234, c_116])).
% 4.06/1.90  tff(c_1264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1254])).
% 4.06/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.90  
% 4.06/1.90  Inference rules
% 4.06/1.90  ----------------------
% 4.06/1.90  #Ref     : 0
% 4.06/1.90  #Sup     : 226
% 4.06/1.90  #Fact    : 0
% 4.06/1.90  #Define  : 0
% 4.06/1.90  #Split   : 13
% 4.06/1.90  #Chain   : 0
% 4.06/1.90  #Close   : 0
% 4.06/1.90  
% 4.06/1.90  Ordering : KBO
% 4.06/1.90  
% 4.06/1.90  Simplification rules
% 4.06/1.90  ----------------------
% 4.06/1.90  #Subsume      : 49
% 4.06/1.90  #Demod        : 169
% 4.06/1.90  #Tautology    : 69
% 4.06/1.90  #SimpNegUnit  : 12
% 4.06/1.90  #BackRed      : 57
% 4.06/1.90  
% 4.06/1.90  #Partial instantiations: 0
% 4.06/1.90  #Strategies tried      : 1
% 4.06/1.90  
% 4.06/1.90  Timing (in seconds)
% 4.06/1.90  ----------------------
% 4.06/1.91  Preprocessing        : 0.43
% 4.06/1.91  Parsing              : 0.22
% 4.06/1.91  CNF conversion       : 0.03
% 4.06/1.91  Main loop            : 0.58
% 4.06/1.91  Inferencing          : 0.22
% 4.06/1.91  Reduction            : 0.18
% 4.06/1.91  Demodulation         : 0.12
% 4.06/1.91  BG Simplification    : 0.03
% 4.06/1.91  Subsumption          : 0.09
% 4.06/1.91  Abstraction          : 0.03
% 4.06/1.91  MUC search           : 0.00
% 4.06/1.91  Cooper               : 0.00
% 4.06/1.91  Total                : 1.05
% 4.06/1.91  Index Insertion      : 0.00
% 4.06/1.91  Index Deletion       : 0.00
% 4.06/1.91  Index Matching       : 0.00
% 4.06/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
