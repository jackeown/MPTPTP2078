%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:42 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 123 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 290 expanded)
%              Number of equality atoms :   32 ( 110 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72,plain,(
    ! [B_43,A_44] :
      ( k1_tarski(k1_funct_1(B_43,A_44)) = k2_relat_1(B_43)
      | k1_tarski(A_44) != k1_relat_1(B_43)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_55,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_relset_1(A_29,B_30,C_31) = k2_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_55])).

tff(c_46,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') != k1_tarski(k1_funct_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    k1_tarski(k1_funct_1('#skF_7','#skF_5')) != k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_46])).

tff(c_78,plain,
    ( k1_tarski('#skF_5') != k1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_60])).

tff(c_85,plain,
    ( k1_tarski('#skF_5') != k1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_78])).

tff(c_87,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_52,plain,(
    v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [B_73,C_74,A_75] :
      ( k1_xboole_0 = B_73
      | r2_hidden(C_74,k1_funct_2(A_75,B_73))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_73)))
      | ~ v1_funct_2(C_74,A_75,B_73)
      | ~ v1_funct_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_159,plain,
    ( k1_xboole_0 = '#skF_6'
    | r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6'))
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_156])).

tff(c_162,plain,
    ( k1_xboole_0 = '#skF_6'
    | r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_159])).

tff(c_163,plain,(
    r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_162])).

tff(c_12,plain,(
    ! [A_6,B_7,D_22] :
      ( '#skF_4'(A_6,B_7,k1_funct_2(A_6,B_7),D_22) = D_22
      | ~ r2_hidden(D_22,k1_funct_2(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_166,plain,(
    '#skF_4'(k1_tarski('#skF_5'),'#skF_6',k1_funct_2(k1_tarski('#skF_5'),'#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_163,c_12])).

tff(c_16,plain,(
    ! [A_6,B_7,D_22] :
      ( v1_relat_1('#skF_4'(A_6,B_7,k1_funct_2(A_6,B_7),D_22))
      | ~ r2_hidden(D_22,k1_funct_2(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_176,plain,
    ( v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_16])).

tff(c_187,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_176])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_187])).

tff(c_190,plain,(
    k1_tarski('#skF_5') != k1_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_232,plain,(
    ! [B_102,C_103,A_104] :
      ( k1_xboole_0 = B_102
      | r2_hidden(C_103,k1_funct_2(A_104,B_102))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_2(C_103,A_104,B_102)
      | ~ v1_funct_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_235,plain,
    ( k1_xboole_0 = '#skF_6'
    | r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6'))
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_232])).

tff(c_238,plain,
    ( k1_xboole_0 = '#skF_6'
    | r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_235])).

tff(c_239,plain,(
    r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_238])).

tff(c_242,plain,(
    '#skF_4'(k1_tarski('#skF_5'),'#skF_6',k1_funct_2(k1_tarski('#skF_5'),'#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_239,c_12])).

tff(c_10,plain,(
    ! [A_6,B_7,D_22] :
      ( k1_relat_1('#skF_4'(A_6,B_7,k1_funct_2(A_6,B_7),D_22)) = A_6
      | ~ r2_hidden(D_22,k1_funct_2(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_249,plain,
    ( k1_tarski('#skF_5') = k1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_10])).

tff(c_261,plain,(
    k1_tarski('#skF_5') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_249])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.50  
% 2.54/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.50  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.54/1.50  
% 2.54/1.50  %Foreground sorts:
% 2.54/1.50  
% 2.54/1.50  
% 2.54/1.50  %Background operators:
% 2.54/1.50  
% 2.54/1.50  
% 2.54/1.50  %Foreground operators:
% 2.54/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.54/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.54/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.50  tff('#skF_7', type, '#skF_7': $i).
% 2.54/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.54/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.54/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.54/1.50  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 2.54/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.54/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.50  
% 2.54/1.52  tff(f_77, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.54/1.52  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.54/1.52  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.54/1.52  tff(f_65, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 2.54/1.52  tff(f_53, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 2.54/1.52  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.52  tff(c_72, plain, (![B_43, A_44]: (k1_tarski(k1_funct_1(B_43, A_44))=k2_relat_1(B_43) | k1_tarski(A_44)!=k1_relat_1(B_43) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.52  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.52  tff(c_55, plain, (![A_29, B_30, C_31]: (k2_relset_1(A_29, B_30, C_31)=k2_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.52  tff(c_59, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_55])).
% 2.54/1.52  tff(c_46, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')!=k1_tarski(k1_funct_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.52  tff(c_60, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))!=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_46])).
% 2.54/1.52  tff(c_78, plain, (k1_tarski('#skF_5')!=k1_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_72, c_60])).
% 2.54/1.52  tff(c_85, plain, (k1_tarski('#skF_5')!=k1_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_78])).
% 2.54/1.52  tff(c_87, plain, (~v1_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_85])).
% 2.54/1.52  tff(c_48, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.52  tff(c_52, plain, (v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.52  tff(c_156, plain, (![B_73, C_74, A_75]: (k1_xboole_0=B_73 | r2_hidden(C_74, k1_funct_2(A_75, B_73)) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_73))) | ~v1_funct_2(C_74, A_75, B_73) | ~v1_funct_1(C_74))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.52  tff(c_159, plain, (k1_xboole_0='#skF_6' | r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6')) | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_156])).
% 2.54/1.52  tff(c_162, plain, (k1_xboole_0='#skF_6' | r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_159])).
% 2.54/1.52  tff(c_163, plain, (r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_162])).
% 2.54/1.52  tff(c_12, plain, (![A_6, B_7, D_22]: ('#skF_4'(A_6, B_7, k1_funct_2(A_6, B_7), D_22)=D_22 | ~r2_hidden(D_22, k1_funct_2(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.52  tff(c_166, plain, ('#skF_4'(k1_tarski('#skF_5'), '#skF_6', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_163, c_12])).
% 2.54/1.52  tff(c_16, plain, (![A_6, B_7, D_22]: (v1_relat_1('#skF_4'(A_6, B_7, k1_funct_2(A_6, B_7), D_22)) | ~r2_hidden(D_22, k1_funct_2(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.52  tff(c_176, plain, (v1_relat_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_16])).
% 2.54/1.52  tff(c_187, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_176])).
% 2.54/1.52  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_187])).
% 2.54/1.52  tff(c_190, plain, (k1_tarski('#skF_5')!=k1_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_85])).
% 2.54/1.52  tff(c_232, plain, (![B_102, C_103, A_104]: (k1_xboole_0=B_102 | r2_hidden(C_103, k1_funct_2(A_104, B_102)) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_2(C_103, A_104, B_102) | ~v1_funct_1(C_103))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.52  tff(c_235, plain, (k1_xboole_0='#skF_6' | r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6')) | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_232])).
% 2.54/1.52  tff(c_238, plain, (k1_xboole_0='#skF_6' | r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_235])).
% 2.54/1.52  tff(c_239, plain, (r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_238])).
% 2.54/1.52  tff(c_242, plain, ('#skF_4'(k1_tarski('#skF_5'), '#skF_6', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_239, c_12])).
% 2.54/1.52  tff(c_10, plain, (![A_6, B_7, D_22]: (k1_relat_1('#skF_4'(A_6, B_7, k1_funct_2(A_6, B_7), D_22))=A_6 | ~r2_hidden(D_22, k1_funct_2(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.52  tff(c_249, plain, (k1_tarski('#skF_5')=k1_relat_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2(k1_tarski('#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_10])).
% 2.54/1.52  tff(c_261, plain, (k1_tarski('#skF_5')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_249])).
% 2.54/1.52  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_261])).
% 2.54/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.52  
% 2.54/1.52  Inference rules
% 2.54/1.52  ----------------------
% 2.54/1.52  #Ref     : 0
% 2.54/1.52  #Sup     : 47
% 2.54/1.52  #Fact    : 0
% 2.54/1.52  #Define  : 0
% 2.54/1.52  #Split   : 1
% 2.54/1.52  #Chain   : 0
% 2.54/1.52  #Close   : 0
% 2.54/1.52  
% 2.54/1.52  Ordering : KBO
% 2.54/1.52  
% 2.54/1.52  Simplification rules
% 2.54/1.52  ----------------------
% 2.54/1.52  #Subsume      : 0
% 2.54/1.52  #Demod        : 11
% 2.54/1.52  #Tautology    : 16
% 2.54/1.52  #SimpNegUnit  : 4
% 2.54/1.52  #BackRed      : 1
% 2.54/1.52  
% 2.54/1.52  #Partial instantiations: 0
% 2.54/1.52  #Strategies tried      : 1
% 2.54/1.52  
% 2.54/1.52  Timing (in seconds)
% 2.54/1.52  ----------------------
% 2.54/1.52  Preprocessing        : 0.41
% 2.54/1.52  Parsing              : 0.18
% 2.54/1.52  CNF conversion       : 0.03
% 2.54/1.52  Main loop            : 0.25
% 2.54/1.52  Inferencing          : 0.10
% 2.54/1.52  Reduction            : 0.07
% 2.54/1.52  Demodulation         : 0.05
% 2.54/1.52  BG Simplification    : 0.03
% 2.54/1.52  Subsumption          : 0.03
% 2.54/1.52  Abstraction          : 0.02
% 2.54/1.52  MUC search           : 0.00
% 2.54/1.52  Cooper               : 0.00
% 2.54/1.52  Total                : 0.71
% 2.54/1.52  Index Insertion      : 0.00
% 2.54/1.52  Index Deletion       : 0.00
% 2.54/1.53  Index Matching       : 0.00
% 2.54/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
