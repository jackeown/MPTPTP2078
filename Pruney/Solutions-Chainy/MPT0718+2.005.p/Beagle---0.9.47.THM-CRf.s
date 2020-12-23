%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:42 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   51 (  63 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 160 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > m1_subset_1 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ~ v2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v5_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),k1_relat_1(A_9))
      | v2_relat_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [C_26,B_27,A_28] :
      ( ~ v1_xboole_0(C_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(C_26))
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_2,A_28] :
      ( ~ v1_xboole_0(A_2)
      | ~ r2_hidden(A_28,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_52,plain,(
    ! [A_28] : ~ r2_hidden(A_28,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_58,plain,(
    ! [A_33] :
      ( v1_xboole_0(k1_funct_1(A_33,'#skF_1'(A_33)))
      | v2_relat_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_62,plain,(
    ! [A_33] :
      ( k1_funct_1(A_33,'#skF_1'(A_33)) = k1_xboole_0
      | v2_relat_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_58,c_4])).

tff(c_134,plain,(
    ! [B_48,C_49,A_50] :
      ( r2_hidden(k1_funct_1(B_48,C_49),k1_funct_1(A_50,C_49))
      | ~ r2_hidden(C_49,k1_relat_1(B_48))
      | ~ v5_funct_1(B_48,A_50)
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    ! [B_48,A_33] :
      ( r2_hidden(k1_funct_1(B_48,'#skF_1'(A_33)),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_33),k1_relat_1(B_48))
      | ~ v5_funct_1(B_48,A_33)
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33)
      | v2_relat_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_134])).

tff(c_161,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden('#skF_1'(A_56),k1_relat_1(B_57))
      | ~ v5_funct_1(B_57,A_56)
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56)
      | v2_relat_1(A_56)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_144])).

tff(c_167,plain,(
    ! [A_56] :
      ( ~ r2_hidden('#skF_1'(A_56),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_56)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56)
      | v2_relat_1(A_56)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_171,plain,(
    ! [A_58] :
      ( ~ r2_hidden('#skF_1'(A_58),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_58)
      | v2_relat_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_167])).

tff(c_175,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_178,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_175])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_178])).

tff(c_181,plain,(
    ! [A_2] : ~ v1_xboole_0(A_2) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  %$ v5_funct_1 > r2_hidden > m1_subset_1 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.36/1.35  
% 2.36/1.35  %Foreground sorts:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Background operators:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Foreground operators:
% 2.36/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.35  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.36/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.35  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.36/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.35  
% 2.36/1.37  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_1)).
% 2.36/1.37  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_funct_1)).
% 2.36/1.37  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.36/1.37  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.36/1.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.36/1.37  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.36/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.36/1.37  tff(c_24, plain, (~v2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.37  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.37  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.37  tff(c_28, plain, (v5_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.37  tff(c_16, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), k1_relat_1(A_9)) | v2_relat_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.36/1.37  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.37  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.37  tff(c_26, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.37  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.37  tff(c_48, plain, (![C_26, B_27, A_28]: (~v1_xboole_0(C_26) | ~m1_subset_1(B_27, k1_zfmisc_1(C_26)) | ~r2_hidden(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.37  tff(c_51, plain, (![A_2, A_28]: (~v1_xboole_0(A_2) | ~r2_hidden(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_48])).
% 2.36/1.37  tff(c_52, plain, (![A_28]: (~r2_hidden(A_28, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_51])).
% 2.36/1.37  tff(c_58, plain, (![A_33]: (v1_xboole_0(k1_funct_1(A_33, '#skF_1'(A_33))) | v2_relat_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.36/1.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.36/1.37  tff(c_62, plain, (![A_33]: (k1_funct_1(A_33, '#skF_1'(A_33))=k1_xboole_0 | v2_relat_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_58, c_4])).
% 2.36/1.37  tff(c_134, plain, (![B_48, C_49, A_50]: (r2_hidden(k1_funct_1(B_48, C_49), k1_funct_1(A_50, C_49)) | ~r2_hidden(C_49, k1_relat_1(B_48)) | ~v5_funct_1(B_48, A_50) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.37  tff(c_144, plain, (![B_48, A_33]: (r2_hidden(k1_funct_1(B_48, '#skF_1'(A_33)), k1_xboole_0) | ~r2_hidden('#skF_1'(A_33), k1_relat_1(B_48)) | ~v5_funct_1(B_48, A_33) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33) | v2_relat_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_62, c_134])).
% 2.36/1.37  tff(c_161, plain, (![A_56, B_57]: (~r2_hidden('#skF_1'(A_56), k1_relat_1(B_57)) | ~v5_funct_1(B_57, A_56) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56) | v2_relat_1(A_56) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(negUnitSimplification, [status(thm)], [c_52, c_144])).
% 2.36/1.37  tff(c_167, plain, (![A_56]: (~r2_hidden('#skF_1'(A_56), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_56) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_56) | ~v1_relat_1(A_56) | v2_relat_1(A_56) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_26, c_161])).
% 2.36/1.37  tff(c_171, plain, (![A_58]: (~r2_hidden('#skF_1'(A_58), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_58) | v2_relat_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_167])).
% 2.36/1.37  tff(c_175, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_171])).
% 2.36/1.37  tff(c_178, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_175])).
% 2.36/1.37  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_178])).
% 2.36/1.37  tff(c_181, plain, (![A_2]: (~v1_xboole_0(A_2))), inference(splitRight, [status(thm)], [c_51])).
% 2.36/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.36/1.37  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_2])).
% 2.36/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.37  
% 2.36/1.37  Inference rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Ref     : 0
% 2.36/1.37  #Sup     : 27
% 2.36/1.37  #Fact    : 0
% 2.36/1.37  #Define  : 0
% 2.36/1.37  #Split   : 2
% 2.36/1.37  #Chain   : 0
% 2.36/1.37  #Close   : 0
% 2.36/1.37  
% 2.36/1.37  Ordering : KBO
% 2.36/1.37  
% 2.36/1.37  Simplification rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Subsume      : 6
% 2.36/1.37  #Demod        : 24
% 2.36/1.37  #Tautology    : 9
% 2.36/1.37  #SimpNegUnit  : 5
% 2.36/1.37  #BackRed      : 1
% 2.36/1.37  
% 2.36/1.37  #Partial instantiations: 0
% 2.36/1.37  #Strategies tried      : 1
% 2.36/1.37  
% 2.36/1.37  Timing (in seconds)
% 2.36/1.37  ----------------------
% 2.58/1.37  Preprocessing        : 0.32
% 2.58/1.37  Parsing              : 0.16
% 2.58/1.37  CNF conversion       : 0.02
% 2.58/1.37  Main loop            : 0.23
% 2.58/1.37  Inferencing          : 0.09
% 2.58/1.37  Reduction            : 0.07
% 2.58/1.37  Demodulation         : 0.05
% 2.58/1.37  BG Simplification    : 0.02
% 2.58/1.37  Subsumption          : 0.04
% 2.58/1.37  Abstraction          : 0.01
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.37  Cooper               : 0.00
% 2.58/1.37  Total                : 0.60
% 2.58/1.37  Index Insertion      : 0.00
% 2.58/1.37  Index Deletion       : 0.00
% 2.58/1.37  Index Matching       : 0.00
% 2.58/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
