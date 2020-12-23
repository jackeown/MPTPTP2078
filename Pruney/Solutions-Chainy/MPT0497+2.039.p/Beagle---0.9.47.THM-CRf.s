%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 113 expanded)
%              Number of equality atoms :   23 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_56,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_34,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_104,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_16,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_169,plain,(
    ! [A_54,B_55] :
      ( k5_relat_1(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_54),k1_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,(
    ! [A_20,B_55] :
      ( k5_relat_1(k6_relat_1(A_20),B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_20,k1_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_169])).

tff(c_193,plain,(
    ! [A_56,B_57] :
      ( k5_relat_1(k6_relat_1(A_56),B_57) = k1_xboole_0
      | ~ r1_xboole_0(A_56,k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_175])).

tff(c_199,plain,
    ( k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_193])).

tff(c_212,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_199])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = k7_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_221,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_30])).

tff(c_228,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_221])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_228])).

tff(c_231,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_258,plain,(
    ! [A_65,C_66,B_67] :
      ( ~ r2_hidden(A_65,C_66)
      | ~ r1_xboole_0(k2_tarski(A_65,B_67),C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_263,plain,(
    ! [A_65] : ~ r2_hidden(A_65,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_258])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_233,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_40])).

tff(c_279,plain,(
    ! [B_73,A_74] :
      ( k3_xboole_0(k1_relat_1(B_73),A_74) = k1_relat_1(k7_relat_1(B_73,A_74))
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_759,plain,(
    ! [B_102,A_103] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_102),A_103),k1_relat_1(k7_relat_1(B_102,A_103)))
      | r1_xboole_0(k1_relat_1(B_102),A_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_4])).

tff(c_789,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_2'),k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_759])).

tff(c_815,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_2'),k1_xboole_0)
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_20,c_789])).

tff(c_817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_263,c_815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.43  
% 2.51/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.43  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.43  
% 2.51/1.43  %Foreground sorts:
% 2.51/1.43  
% 2.51/1.43  
% 2.51/1.43  %Background operators:
% 2.51/1.43  
% 2.51/1.43  
% 2.51/1.43  %Foreground operators:
% 2.51/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.51/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.51/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.43  
% 2.51/1.45  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.51/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.51/1.45  tff(f_56, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.51/1.45  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.51/1.45  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 2.51/1.45  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.51/1.45  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.51/1.45  tff(f_52, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.51/1.45  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.51/1.45  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.51/1.45  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.51/1.45  tff(c_34, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.45  tff(c_78, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.51/1.45  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.45  tff(c_40, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.45  tff(c_104, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_40])).
% 2.51/1.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.45  tff(c_107, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_104, c_2])).
% 2.51/1.45  tff(c_16, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.45  tff(c_26, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.51/1.45  tff(c_169, plain, (![A_54, B_55]: (k5_relat_1(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_54), k1_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.45  tff(c_175, plain, (![A_20, B_55]: (k5_relat_1(k6_relat_1(A_20), B_55)=k1_xboole_0 | ~r1_xboole_0(A_20, k1_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_169])).
% 2.51/1.45  tff(c_193, plain, (![A_56, B_57]: (k5_relat_1(k6_relat_1(A_56), B_57)=k1_xboole_0 | ~r1_xboole_0(A_56, k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_175])).
% 2.51/1.45  tff(c_199, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_107, c_193])).
% 2.51/1.45  tff(c_212, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_199])).
% 2.51/1.45  tff(c_30, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=k7_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.51/1.45  tff(c_221, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_212, c_30])).
% 2.51/1.45  tff(c_228, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_221])).
% 2.51/1.45  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_228])).
% 2.51/1.45  tff(c_231, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.51/1.45  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.45  tff(c_258, plain, (![A_65, C_66, B_67]: (~r2_hidden(A_65, C_66) | ~r1_xboole_0(k2_tarski(A_65, B_67), C_66))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.45  tff(c_263, plain, (![A_65]: (~r2_hidden(A_65, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_258])).
% 2.51/1.45  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.51/1.45  tff(c_233, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_231, c_40])).
% 2.51/1.45  tff(c_279, plain, (![B_73, A_74]: (k3_xboole_0(k1_relat_1(B_73), A_74)=k1_relat_1(k7_relat_1(B_73, A_74)) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.45  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.45  tff(c_759, plain, (![B_102, A_103]: (r2_hidden('#skF_1'(k1_relat_1(B_102), A_103), k1_relat_1(k7_relat_1(B_102, A_103))) | r1_xboole_0(k1_relat_1(B_102), A_103) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_279, c_4])).
% 2.51/1.45  tff(c_789, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_2'), k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_233, c_759])).
% 2.51/1.45  tff(c_815, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_2'), k1_xboole_0) | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_20, c_789])).
% 2.51/1.45  tff(c_817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_263, c_815])).
% 2.51/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.45  
% 2.51/1.45  Inference rules
% 2.51/1.45  ----------------------
% 2.51/1.45  #Ref     : 0
% 2.51/1.45  #Sup     : 166
% 2.51/1.45  #Fact    : 0
% 2.51/1.45  #Define  : 0
% 2.51/1.45  #Split   : 3
% 2.51/1.45  #Chain   : 0
% 2.51/1.45  #Close   : 0
% 2.51/1.45  
% 2.51/1.45  Ordering : KBO
% 2.51/1.45  
% 2.51/1.45  Simplification rules
% 2.51/1.45  ----------------------
% 2.51/1.45  #Subsume      : 27
% 2.51/1.45  #Demod        : 124
% 2.51/1.45  #Tautology    : 92
% 2.51/1.45  #SimpNegUnit  : 11
% 2.51/1.45  #BackRed      : 0
% 2.51/1.45  
% 2.51/1.45  #Partial instantiations: 0
% 2.51/1.45  #Strategies tried      : 1
% 2.51/1.45  
% 2.51/1.45  Timing (in seconds)
% 2.51/1.45  ----------------------
% 2.51/1.45  Preprocessing        : 0.33
% 2.51/1.45  Parsing              : 0.18
% 2.51/1.45  CNF conversion       : 0.02
% 2.51/1.45  Main loop            : 0.30
% 2.51/1.45  Inferencing          : 0.12
% 2.51/1.45  Reduction            : 0.10
% 2.51/1.45  Demodulation         : 0.07
% 2.51/1.45  BG Simplification    : 0.02
% 2.51/1.45  Subsumption          : 0.05
% 2.51/1.45  Abstraction          : 0.02
% 2.51/1.45  MUC search           : 0.00
% 2.51/1.45  Cooper               : 0.00
% 2.51/1.45  Total                : 0.66
% 2.51/1.45  Index Insertion      : 0.00
% 2.51/1.45  Index Deletion       : 0.00
% 2.51/1.45  Index Matching       : 0.00
% 2.51/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
