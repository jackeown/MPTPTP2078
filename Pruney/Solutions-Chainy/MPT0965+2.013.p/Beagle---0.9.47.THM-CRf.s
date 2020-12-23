%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:02 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :   53 (  64 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   79 ( 130 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_89,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_98,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_89])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_64,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_222,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_241,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_222])).

tff(c_910,plain,(
    ! [B_238,A_239,C_240] :
      ( k1_xboole_0 = B_238
      | k1_relset_1(A_239,B_238,C_240) = A_239
      | ~ v1_funct_2(C_240,A_239,B_238)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_933,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_910])).

tff(c_941,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_241,c_933])).

tff(c_942,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_941])).

tff(c_599,plain,(
    ! [A_208,C_209] :
      ( r2_hidden(k4_tarski(A_208,k1_funct_1(C_209,A_208)),C_209)
      | ~ r2_hidden(A_208,k1_relat_1(C_209))
      | ~ v1_funct_1(C_209)
      | ~ v1_relat_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [C_23,A_20,B_21] :
      ( r2_hidden(C_23,A_20)
      | ~ r2_hidden(C_23,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1570,plain,(
    ! [A_330,C_331,A_332] :
      ( r2_hidden(k4_tarski(A_330,k1_funct_1(C_331,A_330)),A_332)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(A_332))
      | ~ r2_hidden(A_330,k1_relat_1(C_331))
      | ~ v1_funct_1(C_331)
      | ~ v1_relat_1(C_331) ) ),
    inference(resolution,[status(thm)],[c_599,c_20])).

tff(c_12,plain,(
    ! [B_10,D_12,A_9,C_11] :
      ( r2_hidden(B_10,D_12)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2771,plain,(
    ! [C_446,A_447,D_448,C_449] :
      ( r2_hidden(k1_funct_1(C_446,A_447),D_448)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(C_449,D_448)))
      | ~ r2_hidden(A_447,k1_relat_1(C_446))
      | ~ v1_funct_1(C_446)
      | ~ v1_relat_1(C_446) ) ),
    inference(resolution,[status(thm)],[c_1570,c_12])).

tff(c_2791,plain,(
    ! [A_447] :
      ( r2_hidden(k1_funct_1('#skF_7',A_447),'#skF_5')
      | ~ r2_hidden(A_447,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_2771])).

tff(c_2801,plain,(
    ! [A_450] :
      ( r2_hidden(k1_funct_1('#skF_7',A_450),'#skF_5')
      | ~ r2_hidden(A_450,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_66,c_942,c_2791])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2814,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_2801,c_56])).

tff(c_2822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:44:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.03  
% 5.43/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.03  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 5.43/2.03  
% 5.43/2.03  %Foreground sorts:
% 5.43/2.03  
% 5.43/2.03  
% 5.43/2.03  %Background operators:
% 5.43/2.03  
% 5.43/2.03  
% 5.43/2.03  %Foreground operators:
% 5.43/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.43/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.43/2.03  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.43/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.43/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.43/2.03  tff('#skF_7', type, '#skF_7': $i).
% 5.43/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.43/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.43/2.03  tff('#skF_6', type, '#skF_6': $i).
% 5.43/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.43/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.43/2.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.43/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.43/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.43/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.43/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.43/2.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.43/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.43/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.43/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.43/2.03  
% 5.43/2.04  tff(f_150, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.43/2.04  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.43/2.04  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.43/2.04  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.43/2.04  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.43/2.04  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.43/2.04  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.43/2.04  tff(c_60, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.43/2.04  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.43/2.04  tff(c_89, plain, (![C_97, A_98, B_99]: (v1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.43/2.04  tff(c_98, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_89])).
% 5.43/2.04  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.43/2.04  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.43/2.04  tff(c_64, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.43/2.04  tff(c_222, plain, (![A_136, B_137, C_138]: (k1_relset_1(A_136, B_137, C_138)=k1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.43/2.04  tff(c_241, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_222])).
% 5.43/2.04  tff(c_910, plain, (![B_238, A_239, C_240]: (k1_xboole_0=B_238 | k1_relset_1(A_239, B_238, C_240)=A_239 | ~v1_funct_2(C_240, A_239, B_238) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.43/2.04  tff(c_933, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_910])).
% 5.43/2.04  tff(c_941, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_241, c_933])).
% 5.43/2.04  tff(c_942, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_941])).
% 5.43/2.04  tff(c_599, plain, (![A_208, C_209]: (r2_hidden(k4_tarski(A_208, k1_funct_1(C_209, A_208)), C_209) | ~r2_hidden(A_208, k1_relat_1(C_209)) | ~v1_funct_1(C_209) | ~v1_relat_1(C_209))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.43/2.04  tff(c_20, plain, (![C_23, A_20, B_21]: (r2_hidden(C_23, A_20) | ~r2_hidden(C_23, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.43/2.04  tff(c_1570, plain, (![A_330, C_331, A_332]: (r2_hidden(k4_tarski(A_330, k1_funct_1(C_331, A_330)), A_332) | ~m1_subset_1(C_331, k1_zfmisc_1(A_332)) | ~r2_hidden(A_330, k1_relat_1(C_331)) | ~v1_funct_1(C_331) | ~v1_relat_1(C_331))), inference(resolution, [status(thm)], [c_599, c_20])).
% 5.43/2.04  tff(c_12, plain, (![B_10, D_12, A_9, C_11]: (r2_hidden(B_10, D_12) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.43/2.04  tff(c_2771, plain, (![C_446, A_447, D_448, C_449]: (r2_hidden(k1_funct_1(C_446, A_447), D_448) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(C_449, D_448))) | ~r2_hidden(A_447, k1_relat_1(C_446)) | ~v1_funct_1(C_446) | ~v1_relat_1(C_446))), inference(resolution, [status(thm)], [c_1570, c_12])).
% 5.43/2.04  tff(c_2791, plain, (![A_447]: (r2_hidden(k1_funct_1('#skF_7', A_447), '#skF_5') | ~r2_hidden(A_447, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_2771])).
% 5.43/2.04  tff(c_2801, plain, (![A_450]: (r2_hidden(k1_funct_1('#skF_7', A_450), '#skF_5') | ~r2_hidden(A_450, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_66, c_942, c_2791])).
% 5.43/2.04  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.43/2.04  tff(c_2814, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_2801, c_56])).
% 5.43/2.04  tff(c_2822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2814])).
% 5.43/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.04  
% 5.43/2.04  Inference rules
% 5.43/2.04  ----------------------
% 5.43/2.04  #Ref     : 0
% 5.43/2.04  #Sup     : 599
% 5.43/2.04  #Fact    : 0
% 5.43/2.04  #Define  : 0
% 5.43/2.04  #Split   : 6
% 5.43/2.04  #Chain   : 0
% 5.43/2.04  #Close   : 0
% 5.43/2.04  
% 5.43/2.04  Ordering : KBO
% 5.43/2.04  
% 5.43/2.04  Simplification rules
% 5.43/2.04  ----------------------
% 5.43/2.04  #Subsume      : 56
% 5.43/2.04  #Demod        : 48
% 5.43/2.04  #Tautology    : 21
% 5.43/2.04  #SimpNegUnit  : 5
% 5.43/2.04  #BackRed      : 1
% 5.43/2.04  
% 5.43/2.04  #Partial instantiations: 0
% 5.43/2.04  #Strategies tried      : 1
% 5.43/2.04  
% 5.43/2.04  Timing (in seconds)
% 5.43/2.04  ----------------------
% 5.43/2.04  Preprocessing        : 0.36
% 5.43/2.04  Parsing              : 0.18
% 5.43/2.04  CNF conversion       : 0.03
% 5.43/2.04  Main loop            : 0.94
% 5.43/2.05  Inferencing          : 0.30
% 5.43/2.05  Reduction            : 0.21
% 5.43/2.05  Demodulation         : 0.14
% 5.43/2.05  BG Simplification    : 0.04
% 5.43/2.05  Subsumption          : 0.31
% 5.43/2.05  Abstraction          : 0.04
% 5.43/2.05  MUC search           : 0.00
% 5.43/2.05  Cooper               : 0.00
% 5.43/2.05  Total                : 1.33
% 5.43/2.05  Index Insertion      : 0.00
% 5.43/2.05  Index Deletion       : 0.00
% 5.43/2.05  Index Matching       : 0.00
% 5.43/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
