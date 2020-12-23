%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   51 (  57 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  86 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [B_40] : k2_xboole_0(B_40,B_40) = B_40 ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_36,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [A_21] : k1_tarski(A_21) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_36])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1842,plain,(
    ! [D_3493,C_3494,B_3495,A_3496] :
      ( r2_hidden(k1_funct_1(D_3493,C_3494),B_3495)
      | k1_xboole_0 = B_3495
      | ~ r2_hidden(C_3494,A_3496)
      | ~ m1_subset_1(D_3493,k1_zfmisc_1(k2_zfmisc_1(A_3496,B_3495)))
      | ~ v1_funct_2(D_3493,A_3496,B_3495)
      | ~ v1_funct_1(D_3493) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2038,plain,(
    ! [D_3921,B_3922] :
      ( r2_hidden(k1_funct_1(D_3921,'#skF_5'),B_3922)
      | k1_xboole_0 = B_3922
      | ~ m1_subset_1(D_3921,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_3922)))
      | ~ v1_funct_2(D_3921,'#skF_3',B_3922)
      | ~ v1_funct_1(D_3921) ) ),
    inference(resolution,[status(thm)],[c_42,c_1842])).

tff(c_2047,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_2038])).

tff(c_2050,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2047])).

tff(c_2051,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2050])).

tff(c_28,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [D_47,B_48,A_49] :
      ( D_47 = B_48
      | D_47 = A_49
      | ~ r2_hidden(D_47,k2_tarski(A_49,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_121,plain,(
    ! [D_47,A_11] :
      ( D_47 = A_11
      | D_47 = A_11
      | ~ r2_hidden(D_47,k1_tarski(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_115])).

tff(c_2056,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2051,c_121])).

tff(c_2102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_2056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.62  
% 3.89/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.89/1.63  
% 3.89/1.63  %Foreground sorts:
% 3.89/1.63  
% 3.89/1.63  
% 3.89/1.63  %Background operators:
% 3.89/1.63  
% 3.89/1.63  
% 3.89/1.63  %Foreground operators:
% 3.89/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.89/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.89/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.89/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.89/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.89/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.89/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.89/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.89/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.89/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.89/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.63  
% 3.89/1.64  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.89/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.89/1.64  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.89/1.64  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.89/1.64  tff(f_67, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.89/1.64  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.89/1.64  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.89/1.64  tff(c_40, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.89/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.64  tff(c_80, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.89/1.64  tff(c_85, plain, (![B_40]: (k2_xboole_0(B_40, B_40)=B_40)), inference(resolution, [status(thm)], [c_6, c_80])).
% 3.89/1.64  tff(c_36, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.89/1.64  tff(c_92, plain, (![A_21]: (k1_tarski(A_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_36])).
% 3.89/1.64  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.89/1.64  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.89/1.64  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.89/1.64  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.89/1.64  tff(c_1842, plain, (![D_3493, C_3494, B_3495, A_3496]: (r2_hidden(k1_funct_1(D_3493, C_3494), B_3495) | k1_xboole_0=B_3495 | ~r2_hidden(C_3494, A_3496) | ~m1_subset_1(D_3493, k1_zfmisc_1(k2_zfmisc_1(A_3496, B_3495))) | ~v1_funct_2(D_3493, A_3496, B_3495) | ~v1_funct_1(D_3493))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.89/1.64  tff(c_2038, plain, (![D_3921, B_3922]: (r2_hidden(k1_funct_1(D_3921, '#skF_5'), B_3922) | k1_xboole_0=B_3922 | ~m1_subset_1(D_3921, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_3922))) | ~v1_funct_2(D_3921, '#skF_3', B_3922) | ~v1_funct_1(D_3921))), inference(resolution, [status(thm)], [c_42, c_1842])).
% 3.89/1.64  tff(c_2047, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_2038])).
% 3.89/1.64  tff(c_2050, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2047])).
% 3.89/1.64  tff(c_2051, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_2050])).
% 3.89/1.64  tff(c_28, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.89/1.64  tff(c_115, plain, (![D_47, B_48, A_49]: (D_47=B_48 | D_47=A_49 | ~r2_hidden(D_47, k2_tarski(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.89/1.64  tff(c_121, plain, (![D_47, A_11]: (D_47=A_11 | D_47=A_11 | ~r2_hidden(D_47, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_115])).
% 3.89/1.64  tff(c_2056, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2051, c_121])).
% 3.89/1.64  tff(c_2102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_2056])).
% 3.89/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.64  
% 3.89/1.64  Inference rules
% 3.89/1.64  ----------------------
% 3.89/1.64  #Ref     : 0
% 3.89/1.64  #Sup     : 251
% 3.89/1.64  #Fact    : 6
% 3.89/1.64  #Define  : 0
% 3.89/1.64  #Split   : 5
% 3.89/1.64  #Chain   : 0
% 3.89/1.64  #Close   : 0
% 3.89/1.64  
% 3.89/1.64  Ordering : KBO
% 3.89/1.64  
% 3.89/1.64  Simplification rules
% 3.89/1.64  ----------------------
% 3.89/1.64  #Subsume      : 44
% 3.89/1.64  #Demod        : 41
% 3.89/1.64  #Tautology    : 87
% 3.89/1.64  #SimpNegUnit  : 16
% 3.89/1.64  #BackRed      : 0
% 3.89/1.64  
% 3.89/1.64  #Partial instantiations: 2256
% 3.89/1.64  #Strategies tried      : 1
% 3.89/1.64  
% 3.89/1.64  Timing (in seconds)
% 3.89/1.64  ----------------------
% 3.89/1.64  Preprocessing        : 0.32
% 3.89/1.64  Parsing              : 0.16
% 3.89/1.64  CNF conversion       : 0.02
% 3.89/1.64  Main loop            : 0.56
% 3.89/1.64  Inferencing          : 0.31
% 3.89/1.64  Reduction            : 0.12
% 3.89/1.64  Demodulation         : 0.08
% 3.89/1.64  BG Simplification    : 0.03
% 3.89/1.64  Subsumption          : 0.06
% 3.89/1.64  Abstraction          : 0.03
% 3.89/1.64  MUC search           : 0.00
% 3.89/1.64  Cooper               : 0.00
% 3.89/1.64  Total                : 0.91
% 3.89/1.64  Index Insertion      : 0.00
% 3.89/1.64  Index Deletion       : 0.00
% 3.89/1.64  Index Matching       : 0.00
% 3.89/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
