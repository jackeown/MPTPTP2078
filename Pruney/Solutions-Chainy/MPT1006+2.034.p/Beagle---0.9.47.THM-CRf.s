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
% DateTime   : Thu Dec  3 10:14:07 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 118 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 ( 179 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_58,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_22,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_41])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_28,A_1] :
      ( A_28 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_28,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_95,plain,(
    ! [A_31,A_30] :
      ( A_31 = A_30
      | ~ m1_subset_1(A_30,k1_tarski(A_31)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_91])).

tff(c_104,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_30,plain,(
    ! [A_15] : k10_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_122,plain,(
    ! [A_15] : k10_relat_1('#skF_5',A_15) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_104,c_30])).

tff(c_24,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [A_9] : m1_subset_1('#skF_5',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_24])).

tff(c_591,plain,(
    ! [A_471,B_472,C_473,D_474] :
      ( k8_relset_1(A_471,B_472,C_473,D_474) = k10_relat_1(C_473,D_474)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_594,plain,(
    ! [A_471,B_472,D_474] : k8_relset_1(A_471,B_472,'#skF_5',D_474) = k10_relat_1('#skF_5',D_474) ),
    inference(resolution,[status(thm)],[c_124,c_591])).

tff(c_600,plain,(
    ! [A_471,B_472,D_474] : k8_relset_1(A_471,B_472,'#skF_5',D_474) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_594])).

tff(c_34,plain,(
    k8_relset_1(k1_xboole_0,'#skF_3','#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,(
    k8_relset_1('#skF_5','#skF_3','#skF_5','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_104,c_34])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.42  
% 2.39/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.39/1.43  
% 2.39/1.43  %Foreground sorts:
% 2.39/1.43  
% 2.39/1.43  
% 2.39/1.43  %Background operators:
% 2.39/1.43  
% 2.39/1.43  
% 2.39/1.43  %Foreground operators:
% 2.39/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.39/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.39/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.39/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.43  
% 2.68/1.44  tff(f_42, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.68/1.44  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.68/1.44  tff(f_71, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.68/1.44  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.68/1.44  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.68/1.44  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.68/1.44  tff(f_58, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.68/1.44  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.44  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.68/1.44  tff(c_22, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.44  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.44  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.68/1.44  tff(c_41, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_36])).
% 2.68/1.44  tff(c_42, plain, (m1_subset_1('#skF_5', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_41])).
% 2.68/1.44  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.44  tff(c_87, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | v1_xboole_0(B_29) | ~m1_subset_1(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.44  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.44  tff(c_91, plain, (![A_28, A_1]: (A_28=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_28, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_87, c_2])).
% 2.68/1.44  tff(c_95, plain, (![A_31, A_30]: (A_31=A_30 | ~m1_subset_1(A_30, k1_tarski(A_31)))), inference(negUnitSimplification, [status(thm)], [c_14, c_91])).
% 2.68/1.44  tff(c_104, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_95])).
% 2.68/1.44  tff(c_30, plain, (![A_15]: (k10_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.68/1.44  tff(c_122, plain, (![A_15]: (k10_relat_1('#skF_5', A_15)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_104, c_30])).
% 2.68/1.44  tff(c_24, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.44  tff(c_124, plain, (![A_9]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_24])).
% 2.68/1.44  tff(c_591, plain, (![A_471, B_472, C_473, D_474]: (k8_relset_1(A_471, B_472, C_473, D_474)=k10_relat_1(C_473, D_474) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_471, B_472))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.68/1.44  tff(c_594, plain, (![A_471, B_472, D_474]: (k8_relset_1(A_471, B_472, '#skF_5', D_474)=k10_relat_1('#skF_5', D_474))), inference(resolution, [status(thm)], [c_124, c_591])).
% 2.68/1.44  tff(c_600, plain, (![A_471, B_472, D_474]: (k8_relset_1(A_471, B_472, '#skF_5', D_474)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_594])).
% 2.68/1.44  tff(c_34, plain, (k8_relset_1(k1_xboole_0, '#skF_3', '#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.68/1.44  tff(c_119, plain, (k8_relset_1('#skF_5', '#skF_3', '#skF_5', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_104, c_34])).
% 2.68/1.44  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_600, c_119])).
% 2.68/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  Inference rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Ref     : 0
% 2.68/1.44  #Sup     : 126
% 2.68/1.44  #Fact    : 1
% 2.68/1.44  #Define  : 0
% 2.68/1.44  #Split   : 1
% 2.68/1.44  #Chain   : 0
% 2.68/1.44  #Close   : 0
% 2.68/1.44  
% 2.68/1.44  Ordering : KBO
% 2.68/1.44  
% 2.68/1.44  Simplification rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Subsume      : 13
% 2.68/1.44  #Demod        : 33
% 2.68/1.44  #Tautology    : 42
% 2.68/1.44  #SimpNegUnit  : 1
% 2.68/1.44  #BackRed      : 11
% 2.68/1.44  
% 2.68/1.44  #Partial instantiations: 297
% 2.68/1.44  #Strategies tried      : 1
% 2.68/1.44  
% 2.68/1.44  Timing (in seconds)
% 2.68/1.44  ----------------------
% 2.68/1.44  Preprocessing        : 0.31
% 2.68/1.44  Parsing              : 0.17
% 2.68/1.44  CNF conversion       : 0.02
% 2.68/1.44  Main loop            : 0.29
% 2.68/1.44  Inferencing          : 0.12
% 2.68/1.44  Reduction            : 0.08
% 2.68/1.44  Demodulation         : 0.06
% 2.68/1.44  BG Simplification    : 0.02
% 2.68/1.44  Subsumption          : 0.05
% 2.68/1.44  Abstraction          : 0.02
% 2.68/1.44  MUC search           : 0.00
% 2.68/1.44  Cooper               : 0.00
% 2.68/1.44  Total                : 0.63
% 2.68/1.44  Index Insertion      : 0.00
% 2.68/1.44  Index Deletion       : 0.00
% 2.68/1.44  Index Matching       : 0.00
% 2.68/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
