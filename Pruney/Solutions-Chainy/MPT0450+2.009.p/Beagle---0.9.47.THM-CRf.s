%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:37 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 271 expanded)
%              Number of leaves         :   38 ( 108 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 429 expanded)
%              Number of equality atoms :   11 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_72,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    ! [A_52,B_53] : r1_xboole_0(k4_xboole_0(A_52,B_53),B_53) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_362,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | ~ r2_hidden(C_91,k3_xboole_0(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_422,plain,(
    ! [A_103,B_104,B_105] :
      ( ~ r1_xboole_0(A_103,B_104)
      | r1_tarski(k3_xboole_0(A_103,B_104),B_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_362])).

tff(c_24,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_136,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_148,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_440,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(A_106,B_107) = k1_xboole_0
      | ~ r1_xboole_0(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_422,c_148])).

tff(c_452,plain,(
    ! [A_24] : k3_xboole_0(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_440])).

tff(c_115,plain,(
    ! [A_67,B_68] : k2_xboole_0(k3_xboole_0(A_67,B_68),k4_xboole_0(A_67,B_68)) = A_67 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,(
    ! [A_24] : k2_xboole_0(k3_xboole_0(A_24,k1_xboole_0),A_24) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_115])).

tff(c_467,plain,(
    ! [A_24] : k2_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_124])).

tff(c_588,plain,(
    ! [A_115,B_116,C_117] : r1_tarski(k2_xboole_0(k3_xboole_0(A_115,B_116),k3_xboole_0(A_115,C_117)),k2_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_602,plain,(
    ! [A_115,A_24] : r1_tarski(k2_xboole_0(k3_xboole_0(A_115,k1_xboole_0),k3_xboole_0(A_115,A_24)),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_588])).

tff(c_625,plain,(
    ! [A_118,A_119] : r1_tarski(k3_xboole_0(A_118,A_119),A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_452,c_602])).

tff(c_44,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_167,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_171,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(A_38)
      | ~ v1_relat_1(B_39)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_44,c_167])).

tff(c_644,plain,(
    ! [A_118,A_119] :
      ( v1_relat_1(k3_xboole_0(A_118,A_119))
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_625,c_171])).

tff(c_621,plain,(
    ! [A_115,A_24] : r1_tarski(k3_xboole_0(A_115,A_24),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_452,c_602])).

tff(c_48,plain,(
    ! [A_43,B_45] :
      ( r1_tarski(k3_relat_1(A_43),k3_relat_1(B_45))
      | ~ r1_tarski(A_43,B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_666,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(A_122,k3_xboole_0(B_123,C_124))
      | ~ r1_tarski(A_122,C_124)
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_686,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_666,c_50])).

tff(c_951,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_686])).

tff(c_954,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_951])).

tff(c_957,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20,c_954])).

tff(c_960,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_644,c_957])).

tff(c_967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_960])).

tff(c_968,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_686])).

tff(c_972,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_968])).

tff(c_975,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_621,c_972])).

tff(c_978,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_644,c_975])).

tff(c_985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:01:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.92  
% 3.47/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.47/1.92  
% 3.47/1.92  %Foreground sorts:
% 3.47/1.92  
% 3.47/1.92  
% 3.47/1.92  %Background operators:
% 3.47/1.92  
% 3.47/1.92  
% 3.47/1.92  %Foreground operators:
% 3.47/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.47/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.92  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.47/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.47/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.47/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.92  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.47/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.92  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.47/1.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.92  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.92  
% 3.47/1.94  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 3.47/1.94  tff(f_68, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.47/1.94  tff(f_72, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.47/1.94  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.47/1.94  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.47/1.94  tff(f_64, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.47/1.94  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/1.94  tff(f_70, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.47/1.94  tff(f_66, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.47/1.94  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.47/1.94  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.94  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 3.47/1.94  tff(f_56, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.47/1.94  tff(f_62, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.47/1.94  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.94  tff(c_28, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.47/1.94  tff(c_68, plain, (![A_52, B_53]: (r1_xboole_0(k4_xboole_0(A_52, B_53), B_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.47/1.94  tff(c_71, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_68])).
% 3.47/1.94  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.94  tff(c_362, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | ~r2_hidden(C_91, k3_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.94  tff(c_422, plain, (![A_103, B_104, B_105]: (~r1_xboole_0(A_103, B_104) | r1_tarski(k3_xboole_0(A_103, B_104), B_105))), inference(resolution, [status(thm)], [c_6, c_362])).
% 3.47/1.94  tff(c_24, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.47/1.94  tff(c_136, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.47/1.94  tff(c_148, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_136])).
% 3.47/1.94  tff(c_440, plain, (![A_106, B_107]: (k3_xboole_0(A_106, B_107)=k1_xboole_0 | ~r1_xboole_0(A_106, B_107))), inference(resolution, [status(thm)], [c_422, c_148])).
% 3.47/1.94  tff(c_452, plain, (![A_24]: (k3_xboole_0(A_24, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_71, c_440])).
% 3.47/1.94  tff(c_115, plain, (![A_67, B_68]: (k2_xboole_0(k3_xboole_0(A_67, B_68), k4_xboole_0(A_67, B_68))=A_67)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.47/1.94  tff(c_124, plain, (![A_24]: (k2_xboole_0(k3_xboole_0(A_24, k1_xboole_0), A_24)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_28, c_115])).
% 3.47/1.94  tff(c_467, plain, (![A_24]: (k2_xboole_0(k1_xboole_0, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_452, c_124])).
% 3.47/1.94  tff(c_588, plain, (![A_115, B_116, C_117]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_115, B_116), k3_xboole_0(A_115, C_117)), k2_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.94  tff(c_602, plain, (![A_115, A_24]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_115, k1_xboole_0), k3_xboole_0(A_115, A_24)), A_24))), inference(superposition, [status(thm), theory('equality')], [c_467, c_588])).
% 3.47/1.94  tff(c_625, plain, (![A_118, A_119]: (r1_tarski(k3_xboole_0(A_118, A_119), A_119))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_452, c_602])).
% 3.47/1.94  tff(c_44, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.47/1.94  tff(c_167, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.47/1.94  tff(c_171, plain, (![A_38, B_39]: (v1_relat_1(A_38) | ~v1_relat_1(B_39) | ~r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_44, c_167])).
% 3.47/1.94  tff(c_644, plain, (![A_118, A_119]: (v1_relat_1(k3_xboole_0(A_118, A_119)) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_625, c_171])).
% 3.47/1.94  tff(c_621, plain, (![A_115, A_24]: (r1_tarski(k3_xboole_0(A_115, A_24), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_452, c_602])).
% 3.47/1.94  tff(c_48, plain, (![A_43, B_45]: (r1_tarski(k3_relat_1(A_43), k3_relat_1(B_45)) | ~r1_tarski(A_43, B_45) | ~v1_relat_1(B_45) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.47/1.94  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.94  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.47/1.94  tff(c_666, plain, (![A_122, B_123, C_124]: (r1_tarski(A_122, k3_xboole_0(B_123, C_124)) | ~r1_tarski(A_122, C_124) | ~r1_tarski(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.47/1.94  tff(c_50, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.94  tff(c_686, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_666, c_50])).
% 3.47/1.94  tff(c_951, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_686])).
% 3.47/1.94  tff(c_954, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_951])).
% 3.47/1.94  tff(c_957, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_20, c_954])).
% 3.47/1.94  tff(c_960, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_644, c_957])).
% 3.47/1.94  tff(c_967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_960])).
% 3.47/1.94  tff(c_968, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_686])).
% 3.47/1.94  tff(c_972, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_968])).
% 3.47/1.94  tff(c_975, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_621, c_972])).
% 3.47/1.94  tff(c_978, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_644, c_975])).
% 3.47/1.94  tff(c_985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_978])).
% 3.47/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.95  
% 3.47/1.95  Inference rules
% 3.47/1.95  ----------------------
% 3.47/1.95  #Ref     : 0
% 3.47/1.95  #Sup     : 221
% 3.47/1.95  #Fact    : 0
% 3.47/1.95  #Define  : 0
% 3.47/1.95  #Split   : 2
% 3.47/1.95  #Chain   : 0
% 3.47/1.95  #Close   : 0
% 3.47/1.95  
% 3.47/1.95  Ordering : KBO
% 3.47/1.95  
% 3.47/1.95  Simplification rules
% 3.47/1.95  ----------------------
% 3.47/1.95  #Subsume      : 20
% 3.47/1.95  #Demod        : 128
% 3.47/1.95  #Tautology    : 144
% 3.47/1.95  #SimpNegUnit  : 7
% 3.47/1.95  #BackRed      : 8
% 3.47/1.95  
% 3.47/1.95  #Partial instantiations: 0
% 3.47/1.95  #Strategies tried      : 1
% 3.47/1.95  
% 3.47/1.95  Timing (in seconds)
% 3.47/1.95  ----------------------
% 3.47/1.95  Preprocessing        : 0.48
% 3.47/1.95  Parsing              : 0.26
% 3.47/1.95  CNF conversion       : 0.03
% 3.47/1.95  Main loop            : 0.52
% 3.47/1.95  Inferencing          : 0.19
% 3.47/1.95  Reduction            : 0.18
% 3.47/1.95  Demodulation         : 0.14
% 3.47/1.95  BG Simplification    : 0.03
% 3.47/1.95  Subsumption          : 0.08
% 3.47/1.95  Abstraction          : 0.03
% 3.47/1.95  MUC search           : 0.00
% 3.47/1.95  Cooper               : 0.00
% 3.47/1.95  Total                : 1.06
% 3.47/1.95  Index Insertion      : 0.00
% 3.47/1.95  Index Deletion       : 0.00
% 3.47/1.95  Index Matching       : 0.00
% 3.47/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
