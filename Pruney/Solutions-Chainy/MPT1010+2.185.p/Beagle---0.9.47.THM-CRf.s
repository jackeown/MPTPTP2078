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
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :   66 (  79 expanded)
%              Number of leaves         :   37 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 116 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_65,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_78,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_108,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    ! [A_42] : r2_hidden(A_42,k1_tarski(A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_64,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    ! [A_28] : k2_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_136,plain,(
    ! [A_56] :
      ( k10_relat_1(A_56,k2_relat_1(A_56)) = k1_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_145,plain,(
    ! [A_28] :
      ( k10_relat_1(k6_relat_1(A_28),A_28) = k1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_136])).

tff(c_149,plain,(
    ! [A_28] : k10_relat_1(k6_relat_1(A_28),A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_145])).

tff(c_191,plain,(
    ! [B_81,A_82] :
      ( k10_relat_1(B_81,k1_tarski(A_82)) != k1_xboole_0
      | ~ r2_hidden(A_82,k2_relat_1(B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_194,plain,(
    ! [A_28,A_82] :
      ( k10_relat_1(k6_relat_1(A_28),k1_tarski(A_82)) != k1_xboole_0
      | ~ r2_hidden(A_82,A_28)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_191])).

tff(c_207,plain,(
    ! [A_85,A_86] :
      ( k10_relat_1(k6_relat_1(A_85),k1_tarski(A_86)) != k1_xboole_0
      | ~ r2_hidden(A_86,A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_194])).

tff(c_211,plain,(
    ! [A_86] :
      ( k1_tarski(A_86) != k1_xboole_0
      | ~ r2_hidden(A_86,k1_tarski(A_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_207])).

tff(c_213,plain,(
    ! [A_86] : k1_tarski(A_86) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_211])).

tff(c_86,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_84,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_80,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2492,plain,(
    ! [D_7575,C_7576,B_7577,A_7578] :
      ( r2_hidden(k1_funct_1(D_7575,C_7576),B_7577)
      | k1_xboole_0 = B_7577
      | ~ r2_hidden(C_7576,A_7578)
      | ~ m1_subset_1(D_7575,k1_zfmisc_1(k2_zfmisc_1(A_7578,B_7577)))
      | ~ v1_funct_2(D_7575,A_7578,B_7577)
      | ~ v1_funct_1(D_7575) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3558,plain,(
    ! [D_9415,B_9416] :
      ( r2_hidden(k1_funct_1(D_9415,'#skF_7'),B_9416)
      | k1_xboole_0 = B_9416
      | ~ m1_subset_1(D_9415,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_9416)))
      | ~ v1_funct_2(D_9415,'#skF_5',B_9416)
      | ~ v1_funct_1(D_9415) ) ),
    inference(resolution,[status(thm)],[c_80,c_2492])).

tff(c_3567,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_3558])).

tff(c_3570,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_3567])).

tff(c_3571,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_3570])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_171,plain,(
    ! [D_76,B_77,A_78] :
      ( D_76 = B_77
      | D_76 = A_78
      | ~ r2_hidden(D_76,k2_tarski(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_174,plain,(
    ! [D_76,A_7] :
      ( D_76 = A_7
      | D_76 = A_7
      | ~ r2_hidden(D_76,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_171])).

tff(c_3578,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3571,c_174])).

tff(c_3633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_3578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:49 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.97  
% 4.82/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.97  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_4
% 4.82/1.97  
% 4.82/1.97  %Foreground sorts:
% 4.82/1.97  
% 4.82/1.97  
% 4.82/1.97  %Background operators:
% 4.82/1.97  
% 4.82/1.97  
% 4.82/1.97  %Foreground operators:
% 4.82/1.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.82/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.82/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.82/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.82/1.97  tff('#skF_7', type, '#skF_7': $i).
% 4.82/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.82/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.82/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.82/1.97  tff('#skF_5', type, '#skF_5': $i).
% 4.82/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.82/1.97  tff('#skF_6', type, '#skF_6': $i).
% 4.82/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.82/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.82/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.82/1.97  tff('#skF_8', type, '#skF_8': $i).
% 4.82/1.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.97  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.82/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.82/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.82/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.82/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.82/1.97  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.97  
% 4.82/1.99  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.82/1.99  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.82/1.99  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.82/1.99  tff(f_65, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.82/1.99  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.82/1.99  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.82/1.99  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 4.82/1.99  tff(f_92, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.82/1.99  tff(c_78, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.99  tff(c_108, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.82/1.99  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.82/1.99  tff(c_114, plain, (![A_42]: (r2_hidden(A_42, k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_6])).
% 4.82/1.99  tff(c_64, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.82/1.99  tff(c_68, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.82/1.99  tff(c_70, plain, (![A_28]: (k2_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.82/1.99  tff(c_136, plain, (![A_56]: (k10_relat_1(A_56, k2_relat_1(A_56))=k1_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.82/1.99  tff(c_145, plain, (![A_28]: (k10_relat_1(k6_relat_1(A_28), A_28)=k1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_136])).
% 4.82/1.99  tff(c_149, plain, (![A_28]: (k10_relat_1(k6_relat_1(A_28), A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_145])).
% 4.82/1.99  tff(c_191, plain, (![B_81, A_82]: (k10_relat_1(B_81, k1_tarski(A_82))!=k1_xboole_0 | ~r2_hidden(A_82, k2_relat_1(B_81)) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.82/1.99  tff(c_194, plain, (![A_28, A_82]: (k10_relat_1(k6_relat_1(A_28), k1_tarski(A_82))!=k1_xboole_0 | ~r2_hidden(A_82, A_28) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_191])).
% 4.82/1.99  tff(c_207, plain, (![A_85, A_86]: (k10_relat_1(k6_relat_1(A_85), k1_tarski(A_86))!=k1_xboole_0 | ~r2_hidden(A_86, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_194])).
% 4.82/1.99  tff(c_211, plain, (![A_86]: (k1_tarski(A_86)!=k1_xboole_0 | ~r2_hidden(A_86, k1_tarski(A_86)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_207])).
% 4.82/1.99  tff(c_213, plain, (![A_86]: (k1_tarski(A_86)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_211])).
% 4.82/1.99  tff(c_86, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.99  tff(c_84, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.99  tff(c_82, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.99  tff(c_80, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.99  tff(c_2492, plain, (![D_7575, C_7576, B_7577, A_7578]: (r2_hidden(k1_funct_1(D_7575, C_7576), B_7577) | k1_xboole_0=B_7577 | ~r2_hidden(C_7576, A_7578) | ~m1_subset_1(D_7575, k1_zfmisc_1(k2_zfmisc_1(A_7578, B_7577))) | ~v1_funct_2(D_7575, A_7578, B_7577) | ~v1_funct_1(D_7575))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.82/1.99  tff(c_3558, plain, (![D_9415, B_9416]: (r2_hidden(k1_funct_1(D_9415, '#skF_7'), B_9416) | k1_xboole_0=B_9416 | ~m1_subset_1(D_9415, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_9416))) | ~v1_funct_2(D_9415, '#skF_5', B_9416) | ~v1_funct_1(D_9415))), inference(resolution, [status(thm)], [c_80, c_2492])).
% 4.82/1.99  tff(c_3567, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_82, c_3558])).
% 4.82/1.99  tff(c_3570, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_3567])).
% 4.82/1.99  tff(c_3571, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_213, c_3570])).
% 4.82/1.99  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.82/1.99  tff(c_171, plain, (![D_76, B_77, A_78]: (D_76=B_77 | D_76=A_78 | ~r2_hidden(D_76, k2_tarski(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.82/1.99  tff(c_174, plain, (![D_76, A_7]: (D_76=A_7 | D_76=A_7 | ~r2_hidden(D_76, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_171])).
% 4.82/1.99  tff(c_3578, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_3571, c_174])).
% 4.82/1.99  tff(c_3633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_78, c_3578])).
% 4.82/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.99  
% 4.82/1.99  Inference rules
% 4.82/1.99  ----------------------
% 4.82/1.99  #Ref     : 0
% 4.82/1.99  #Sup     : 447
% 4.82/1.99  #Fact    : 8
% 4.82/1.99  #Define  : 0
% 4.82/1.99  #Split   : 5
% 4.82/1.99  #Chain   : 0
% 4.82/1.99  #Close   : 0
% 4.82/1.99  
% 4.82/1.99  Ordering : KBO
% 4.82/1.99  
% 4.82/1.99  Simplification rules
% 4.82/1.99  ----------------------
% 4.82/1.99  #Subsume      : 67
% 4.82/1.99  #Demod        : 77
% 4.82/1.99  #Tautology    : 147
% 4.82/1.99  #SimpNegUnit  : 18
% 4.82/1.99  #BackRed      : 0
% 4.82/1.99  
% 4.82/1.99  #Partial instantiations: 4599
% 4.82/1.99  #Strategies tried      : 1
% 4.82/1.99  
% 4.82/1.99  Timing (in seconds)
% 4.82/1.99  ----------------------
% 4.82/1.99  Preprocessing        : 0.35
% 4.82/1.99  Parsing              : 0.17
% 4.82/1.99  CNF conversion       : 0.03
% 4.82/1.99  Main loop            : 0.87
% 4.82/1.99  Inferencing          : 0.45
% 4.82/1.99  Reduction            : 0.20
% 4.82/1.99  Demodulation         : 0.14
% 4.82/1.99  BG Simplification    : 0.04
% 4.82/1.99  Subsumption          : 0.12
% 4.82/1.99  Abstraction          : 0.05
% 4.82/1.99  MUC search           : 0.00
% 4.82/1.99  Cooper               : 0.00
% 4.82/1.99  Total                : 1.25
% 4.82/1.99  Index Insertion      : 0.00
% 4.82/1.99  Index Deletion       : 0.00
% 4.82/1.99  Index Matching       : 0.00
% 4.82/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
