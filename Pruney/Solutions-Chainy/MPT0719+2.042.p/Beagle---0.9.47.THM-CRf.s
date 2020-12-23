%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:48 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 152 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(B) )
     => ( v1_xboole_0(k5_relat_1(A,B))
        & v1_relat_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_relat_1)).

tff(f_46,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_80,axiom,(
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

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    ! [A_28] :
      ( k5_relat_1(k1_xboole_0,A_28) = k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    k5_relat_1(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_94,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_94])).

tff(c_110,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40,c_106])).

tff(c_14,plain,(
    ! [A_8] : k10_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_206,plain,(
    ! [B_44,A_45] :
      ( k10_relat_1(B_44,k1_tarski(A_45)) != k1_xboole_0
      | ~ r2_hidden(A_45,k2_relat_1(B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_209,plain,(
    ! [A_45] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_45)) != k1_xboole_0
      | ~ r2_hidden(A_45,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_206])).

tff(c_211,plain,(
    ! [A_45] : ~ r2_hidden(A_45,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_14,c_209])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_111,plain,(
    ! [B_34,A_35] :
      ( v1_funct_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_115,plain,(
    ! [A_2] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_144,plain,(
    ! [A_39] :
      ( ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_153,plain,(
    ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_144])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_153])).

tff(c_160,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_278,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),k1_relat_1(B_52))
      | v5_funct_1(B_52,A_51)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_281,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_1'(A_51,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_51)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_278])).

tff(c_283,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_1'(A_51,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_160,c_281])).

tff(c_285,plain,(
    ! [A_53] :
      ( v5_funct_1(k1_xboole_0,A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_283])).

tff(c_36,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_288,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_285,c_36])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.66  
% 2.53/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.67  %$ v5_funct_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.53/1.67  
% 2.53/1.67  %Foreground sorts:
% 2.53/1.67  
% 2.53/1.67  
% 2.53/1.67  %Background operators:
% 2.53/1.67  
% 2.53/1.67  
% 2.53/1.67  %Foreground operators:
% 2.53/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.53/1.67  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.53/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.67  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.53/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.53/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.67  
% 2.68/1.69  tff(f_94, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.68/1.69  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.69  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.68/1.69  tff(f_44, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(B)) => (v1_xboole_0(k5_relat_1(A, B)) & v1_relat_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_relat_1)).
% 2.68/1.69  tff(f_46, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.68/1.69  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.68/1.69  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.68/1.69  tff(f_30, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.69  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_1)).
% 2.68/1.69  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.68/1.69  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.69  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.69  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.68/1.69  tff(c_66, plain, (![A_28]: (k5_relat_1(k1_xboole_0, A_28)=k1_xboole_0 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.69  tff(c_70, plain, (k5_relat_1(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_66])).
% 2.68/1.69  tff(c_94, plain, (![A_32, B_33]: (v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.69  tff(c_106, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_94])).
% 2.68/1.69  tff(c_110, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40, c_106])).
% 2.68/1.69  tff(c_14, plain, (![A_8]: (k10_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.69  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.69  tff(c_206, plain, (![B_44, A_45]: (k10_relat_1(B_44, k1_tarski(A_45))!=k1_xboole_0 | ~r2_hidden(A_45, k2_relat_1(B_44)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.68/1.69  tff(c_209, plain, (![A_45]: (k10_relat_1(k1_xboole_0, k1_tarski(A_45))!=k1_xboole_0 | ~r2_hidden(A_45, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_206])).
% 2.68/1.69  tff(c_211, plain, (![A_45]: (~r2_hidden(A_45, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_14, c_209])).
% 2.68/1.69  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.68/1.69  tff(c_111, plain, (![B_34, A_35]: (v1_funct_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.69  tff(c_115, plain, (![A_2]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(resolution, [status(thm)], [c_6, c_111])).
% 2.68/1.69  tff(c_144, plain, (![A_39]: (~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(splitLeft, [status(thm)], [c_115])).
% 2.68/1.69  tff(c_153, plain, (~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_144])).
% 2.68/1.69  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_153])).
% 2.68/1.69  tff(c_160, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_115])).
% 2.68/1.69  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.69  tff(c_278, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), k1_relat_1(B_52)) | v5_funct_1(B_52, A_51) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.68/1.69  tff(c_281, plain, (![A_51]: (r2_hidden('#skF_1'(A_51, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_51) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_18, c_278])).
% 2.68/1.69  tff(c_283, plain, (![A_51]: (r2_hidden('#skF_1'(A_51, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_160, c_281])).
% 2.68/1.69  tff(c_285, plain, (![A_53]: (v5_funct_1(k1_xboole_0, A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(negUnitSimplification, [status(thm)], [c_211, c_283])).
% 2.68/1.69  tff(c_36, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.69  tff(c_288, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_285, c_36])).
% 2.68/1.69  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_288])).
% 2.68/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.69  
% 2.68/1.69  Inference rules
% 2.68/1.69  ----------------------
% 2.68/1.69  #Ref     : 0
% 2.68/1.69  #Sup     : 56
% 2.68/1.69  #Fact    : 0
% 2.68/1.69  #Define  : 0
% 2.68/1.69  #Split   : 1
% 2.68/1.69  #Chain   : 0
% 2.68/1.69  #Close   : 0
% 2.68/1.69  
% 2.68/1.69  Ordering : KBO
% 2.68/1.69  
% 2.68/1.69  Simplification rules
% 2.68/1.69  ----------------------
% 2.68/1.69  #Subsume      : 2
% 2.68/1.69  #Demod        : 58
% 2.68/1.69  #Tautology    : 42
% 2.68/1.69  #SimpNegUnit  : 2
% 2.68/1.69  #BackRed      : 0
% 2.68/1.69  
% 2.68/1.69  #Partial instantiations: 0
% 2.68/1.69  #Strategies tried      : 1
% 2.68/1.69  
% 2.68/1.69  Timing (in seconds)
% 2.68/1.69  ----------------------
% 2.68/1.69  Preprocessing        : 0.48
% 2.68/1.69  Parsing              : 0.25
% 2.68/1.69  CNF conversion       : 0.03
% 2.68/1.69  Main loop            : 0.30
% 2.68/1.69  Inferencing          : 0.12
% 2.68/1.69  Reduction            : 0.09
% 2.68/1.69  Demodulation         : 0.07
% 2.68/1.69  BG Simplification    : 0.02
% 2.68/1.69  Subsumption          : 0.05
% 2.68/1.69  Abstraction          : 0.02
% 2.68/1.69  MUC search           : 0.00
% 2.68/1.69  Cooper               : 0.00
% 2.68/1.69  Total                : 0.83
% 2.68/1.69  Index Insertion      : 0.00
% 2.68/1.69  Index Deletion       : 0.00
% 2.68/1.69  Index Matching       : 0.00
% 2.68/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
