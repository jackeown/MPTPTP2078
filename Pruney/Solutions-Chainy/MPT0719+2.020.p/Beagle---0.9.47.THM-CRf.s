%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 (  86 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_61,plain,(
    ! [A_28] : r1_tarski('#skF_1'(A_28),A_28) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_78,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8])).

tff(c_14,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_78,c_14])).

tff(c_104,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_48,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_43,plain,(
    ! [A_21] :
      ( v1_funct_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_47,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41),k1_relat_1(B_41))
      | v5_funct_1(B_41,A_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_120,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_40)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_115])).

tff(c_123,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_47,c_120])).

tff(c_126,plain,(
    ! [A_44] :
      ( v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_123])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_129,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_30])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  %$ v5_funct_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.88/1.20  
% 1.88/1.20  %Foreground sorts:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Background operators:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Foreground operators:
% 1.88/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.20  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.88/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.20  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.88/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.20  
% 1.88/1.22  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.88/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.22  tff(f_36, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 1.88/1.22  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.88/1.22  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.88/1.22  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.88/1.22  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.88/1.22  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.88/1.22  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.22  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.88/1.22  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.22  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.88/1.22  tff(c_8, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.22  tff(c_56, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.22  tff(c_61, plain, (![A_28]: (r1_tarski('#skF_1'(A_28), A_28))), inference(resolution, [status(thm)], [c_8, c_56])).
% 1.88/1.22  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.88/1.22  tff(c_66, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_4])).
% 1.88/1.22  tff(c_78, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_8])).
% 1.88/1.22  tff(c_14, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.22  tff(c_98, plain, (![A_6]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_78, c_14])).
% 1.88/1.22  tff(c_104, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_98])).
% 1.88/1.22  tff(c_48, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.22  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_48])).
% 1.88/1.22  tff(c_43, plain, (![A_21]: (v1_funct_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.22  tff(c_47, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.88/1.22  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.22  tff(c_115, plain, (![A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41), k1_relat_1(B_41)) | v5_funct_1(B_41, A_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.88/1.22  tff(c_120, plain, (![A_40]: (r2_hidden('#skF_2'(A_40, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_40) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_20, c_115])).
% 1.88/1.22  tff(c_123, plain, (![A_40]: (r2_hidden('#skF_2'(A_40, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_47, c_120])).
% 1.88/1.22  tff(c_126, plain, (![A_44]: (v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(negUnitSimplification, [status(thm)], [c_104, c_123])).
% 1.88/1.22  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.22  tff(c_129, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_30])).
% 1.88/1.22  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_129])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 23
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 0
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 1
% 1.88/1.22  #Demod        : 7
% 1.88/1.22  #Tautology    : 9
% 1.88/1.22  #SimpNegUnit  : 1
% 1.88/1.22  #BackRed      : 0
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.22  Preprocessing        : 0.28
% 1.88/1.22  Parsing              : 0.16
% 1.88/1.22  CNF conversion       : 0.02
% 1.88/1.22  Main loop            : 0.16
% 1.88/1.22  Inferencing          : 0.06
% 1.88/1.22  Reduction            : 0.04
% 1.88/1.22  Demodulation         : 0.03
% 1.88/1.22  BG Simplification    : 0.01
% 1.88/1.22  Subsumption          : 0.03
% 1.88/1.22  Abstraction          : 0.01
% 1.88/1.22  MUC search           : 0.00
% 1.88/1.22  Cooper               : 0.00
% 1.88/1.22  Total                : 0.47
% 1.88/1.22  Index Insertion      : 0.00
% 1.88/1.22  Index Deletion       : 0.00
% 1.88/1.22  Index Matching       : 0.00
% 1.88/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
