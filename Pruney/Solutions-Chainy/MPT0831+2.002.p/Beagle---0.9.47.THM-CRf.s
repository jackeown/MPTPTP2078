%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:32 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  77 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_95,plain,(
    ! [A_51,B_52,D_53] :
      ( r2_relset_1(A_51,B_52,D_53,D_53)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_98,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_95])).

tff(c_33,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [C_85,B_88,D_87,A_84,E_86] :
      ( m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(B_88,D_87)))
      | ~ r1_tarski(C_85,D_87)
      | ~ r1_tarski(A_84,B_88)
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_84,C_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_175,plain,(
    ! [E_89,B_90,B_91,A_92] :
      ( m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(B_90,B_91)))
      | ~ r1_tarski(A_92,B_90)
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_200,plain,(
    ! [E_93,B_94] :
      ( m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_94)))
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_94))) ) ),
    inference(resolution,[status(thm)],[c_28,c_175])).

tff(c_204,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_222,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_204,c_16])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_227,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_222,c_10])).

tff(c_230,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_227])).

tff(c_127,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k5_relset_1(A_72,B_73,C_74,D_75) = k7_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,(
    ! [D_75] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_75) = k7_relat_1('#skF_4',D_75) ),
    inference(resolution,[status(thm)],[c_30,c_127])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_231,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_131])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.23  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.23  
% 2.14/1.23  %Foreground sorts:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Background operators:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Foreground operators:
% 2.14/1.23  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.14/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.23  
% 2.14/1.25  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.14/1.25  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.14/1.25  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.25  tff(f_71, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.14/1.25  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.25  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.14/1.25  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.14/1.25  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.25  tff(c_95, plain, (![A_51, B_52, D_53]: (r2_relset_1(A_51, B_52, D_53, D_53) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.25  tff(c_98, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_95])).
% 2.14/1.25  tff(c_33, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.25  tff(c_37, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_33])).
% 2.14/1.25  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.25  tff(c_150, plain, (![C_85, B_88, D_87, A_84, E_86]: (m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(B_88, D_87))) | ~r1_tarski(C_85, D_87) | ~r1_tarski(A_84, B_88) | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_84, C_85))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.14/1.25  tff(c_175, plain, (![E_89, B_90, B_91, A_92]: (m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(B_90, B_91))) | ~r1_tarski(A_92, B_90) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(resolution, [status(thm)], [c_6, c_150])).
% 2.14/1.25  tff(c_200, plain, (![E_93, B_94]: (m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_94))) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_94))))), inference(resolution, [status(thm)], [c_28, c_175])).
% 2.14/1.25  tff(c_204, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_30, c_200])).
% 2.14/1.25  tff(c_16, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.25  tff(c_222, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_204, c_16])).
% 2.14/1.25  tff(c_10, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.25  tff(c_227, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_222, c_10])).
% 2.14/1.25  tff(c_230, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37, c_227])).
% 2.14/1.25  tff(c_127, plain, (![A_72, B_73, C_74, D_75]: (k5_relset_1(A_72, B_73, C_74, D_75)=k7_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.25  tff(c_130, plain, (![D_75]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_75)=k7_relat_1('#skF_4', D_75))), inference(resolution, [status(thm)], [c_30, c_127])).
% 2.14/1.25  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.25  tff(c_131, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_26])).
% 2.14/1.25  tff(c_231, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_131])).
% 2.14/1.25  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_231])).
% 2.14/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  Inference rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Ref     : 0
% 2.14/1.25  #Sup     : 48
% 2.14/1.25  #Fact    : 0
% 2.14/1.25  #Define  : 0
% 2.14/1.25  #Split   : 1
% 2.14/1.25  #Chain   : 0
% 2.14/1.25  #Close   : 0
% 2.14/1.25  
% 2.14/1.25  Ordering : KBO
% 2.14/1.25  
% 2.14/1.25  Simplification rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Subsume      : 0
% 2.14/1.25  #Demod        : 9
% 2.14/1.25  #Tautology    : 9
% 2.14/1.25  #SimpNegUnit  : 0
% 2.14/1.25  #BackRed      : 2
% 2.14/1.25  
% 2.14/1.25  #Partial instantiations: 0
% 2.14/1.25  #Strategies tried      : 1
% 2.14/1.25  
% 2.14/1.25  Timing (in seconds)
% 2.14/1.25  ----------------------
% 2.14/1.25  Preprocessing        : 0.29
% 2.14/1.25  Parsing              : 0.15
% 2.14/1.25  CNF conversion       : 0.02
% 2.14/1.25  Main loop            : 0.19
% 2.14/1.25  Inferencing          : 0.07
% 2.14/1.25  Reduction            : 0.06
% 2.14/1.25  Demodulation         : 0.05
% 2.14/1.25  BG Simplification    : 0.01
% 2.14/1.25  Subsumption          : 0.04
% 2.14/1.25  Abstraction          : 0.01
% 2.14/1.25  MUC search           : 0.00
% 2.14/1.25  Cooper               : 0.00
% 2.14/1.25  Total                : 0.51
% 2.14/1.25  Index Insertion      : 0.00
% 2.14/1.25  Index Deletion       : 0.00
% 2.14/1.25  Index Matching       : 0.00
% 2.14/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
