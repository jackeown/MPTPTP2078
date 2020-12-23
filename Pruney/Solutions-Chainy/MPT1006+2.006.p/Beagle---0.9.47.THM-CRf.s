%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:03 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 340 expanded)
%              Number of leaves         :   36 ( 132 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 610 expanded)
%              Number of equality atoms :   37 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_59,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_143,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_xboole_0(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_146,plain,(
    ! [C_46] :
      ( v1_xboole_0(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_158,plain,(
    ! [C_49] :
      ( v1_xboole_0(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_166,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_158])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_166,c_4])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_194,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_14])).

tff(c_303,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( k8_relset_1(A_68,B_69,C_70,D_71) = k10_relat_1(C_70,D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_311,plain,(
    ! [A_68,B_69,D_71] : k8_relset_1(A_68,B_69,'#skF_3',D_71) = k10_relat_1('#skF_3',D_71) ),
    inference(resolution,[status(thm)],[c_194,c_303])).

tff(c_442,plain,(
    ! [A_99,B_100,C_101] :
      ( k8_relset_1(A_99,B_100,C_101,B_100) = k1_relset_1(A_99,B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_451,plain,(
    ! [A_99,B_100] : k8_relset_1(A_99,B_100,'#skF_3',B_100) = k1_relset_1(A_99,B_100,'#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_442])).

tff(c_455,plain,(
    ! [A_102,B_103] : k1_relset_1(A_102,B_103,'#skF_3') = k10_relat_1('#skF_3',B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_451])).

tff(c_102,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    ! [C_39] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_123])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_195,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_6])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_196,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_18])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_197,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_20])).

tff(c_249,plain,(
    ! [B_56,A_57] :
      ( v1_funct_2(B_56,k1_relat_1(B_56),A_57)
      | ~ r1_tarski(k2_relat_1(B_56),A_57)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_252,plain,(
    ! [A_57] :
      ( v1_funct_2('#skF_3','#skF_3',A_57)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_57)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_249])).

tff(c_254,plain,(
    ! [A_57] : v1_funct_2('#skF_3','#skF_3',A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_56,c_195,c_196,c_252])).

tff(c_40,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_335,plain,(
    ! [B_77,C_78] :
      ( k1_relset_1('#skF_3',B_77,C_78) = '#skF_3'
      | ~ v1_funct_2(C_78,'#skF_3',B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_172,c_172,c_60])).

tff(c_340,plain,(
    ! [A_57] :
      ( k1_relset_1('#skF_3',A_57,'#skF_3') = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_254,c_335])).

tff(c_347,plain,(
    ! [A_57] : k1_relset_1('#skF_3',A_57,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_340])).

tff(c_461,plain,(
    ! [B_103] : k10_relat_1('#skF_3',B_103) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_347])).

tff(c_50,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_190,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_50])).

tff(c_324,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_190])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.31  
% 2.29/1.31  %Foreground sorts:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Background operators:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Foreground operators:
% 2.29/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.29/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.31  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.29/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.29/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.29/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.29/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.29/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.31  
% 2.58/1.33  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.58/1.33  tff(f_109, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.58/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.33  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.58/1.33  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.58/1.33  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.58/1.33  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.58/1.33  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.58/1.33  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.33  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.58/1.33  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.58/1.33  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 2.58/1.33  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.58/1.33  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.33  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.58/1.33  tff(c_59, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_52])).
% 2.58/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.33  tff(c_143, plain, (![C_46, A_47, B_48]: (v1_xboole_0(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.33  tff(c_146, plain, (![C_46]: (v1_xboole_0(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_143])).
% 2.58/1.33  tff(c_158, plain, (![C_49]: (v1_xboole_0(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_146])).
% 2.58/1.33  tff(c_166, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_59, c_158])).
% 2.58/1.33  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.58/1.33  tff(c_172, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_166, c_4])).
% 2.58/1.33  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.33  tff(c_194, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_14])).
% 2.58/1.33  tff(c_303, plain, (![A_68, B_69, C_70, D_71]: (k8_relset_1(A_68, B_69, C_70, D_71)=k10_relat_1(C_70, D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.33  tff(c_311, plain, (![A_68, B_69, D_71]: (k8_relset_1(A_68, B_69, '#skF_3', D_71)=k10_relat_1('#skF_3', D_71))), inference(resolution, [status(thm)], [c_194, c_303])).
% 2.58/1.33  tff(c_442, plain, (![A_99, B_100, C_101]: (k8_relset_1(A_99, B_100, C_101, B_100)=k1_relset_1(A_99, B_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.58/1.33  tff(c_451, plain, (![A_99, B_100]: (k8_relset_1(A_99, B_100, '#skF_3', B_100)=k1_relset_1(A_99, B_100, '#skF_3'))), inference(resolution, [status(thm)], [c_194, c_442])).
% 2.58/1.33  tff(c_455, plain, (![A_102, B_103]: (k1_relset_1(A_102, B_103, '#skF_3')=k10_relat_1('#skF_3', B_103))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_451])).
% 2.58/1.33  tff(c_102, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.33  tff(c_123, plain, (![C_39]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_102])).
% 2.58/1.33  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_59, c_123])).
% 2.58/1.33  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.58/1.33  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.33  tff(c_195, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_6])).
% 2.58/1.33  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.33  tff(c_196, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_18])).
% 2.58/1.33  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.33  tff(c_197, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_20])).
% 2.58/1.33  tff(c_249, plain, (![B_56, A_57]: (v1_funct_2(B_56, k1_relat_1(B_56), A_57) | ~r1_tarski(k2_relat_1(B_56), A_57) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.33  tff(c_252, plain, (![A_57]: (v1_funct_2('#skF_3', '#skF_3', A_57) | ~r1_tarski(k2_relat_1('#skF_3'), A_57) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_249])).
% 2.58/1.33  tff(c_254, plain, (![A_57]: (v1_funct_2('#skF_3', '#skF_3', A_57))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_56, c_195, c_196, c_252])).
% 2.58/1.33  tff(c_40, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.58/1.33  tff(c_60, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 2.58/1.33  tff(c_335, plain, (![B_77, C_78]: (k1_relset_1('#skF_3', B_77, C_78)='#skF_3' | ~v1_funct_2(C_78, '#skF_3', B_77) | ~m1_subset_1(C_78, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_172, c_172, c_60])).
% 2.58/1.33  tff(c_340, plain, (![A_57]: (k1_relset_1('#skF_3', A_57, '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_254, c_335])).
% 2.58/1.33  tff(c_347, plain, (![A_57]: (k1_relset_1('#skF_3', A_57, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_340])).
% 2.58/1.33  tff(c_461, plain, (![B_103]: (k10_relat_1('#skF_3', B_103)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_455, c_347])).
% 2.58/1.33  tff(c_50, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.58/1.33  tff(c_190, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_50])).
% 2.58/1.33  tff(c_324, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_311, c_190])).
% 2.58/1.33  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_324])).
% 2.58/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.33  
% 2.58/1.33  Inference rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Ref     : 0
% 2.58/1.33  #Sup     : 89
% 2.58/1.33  #Fact    : 0
% 2.58/1.33  #Define  : 0
% 2.58/1.33  #Split   : 0
% 2.58/1.33  #Chain   : 0
% 2.58/1.33  #Close   : 0
% 2.58/1.33  
% 2.58/1.33  Ordering : KBO
% 2.58/1.33  
% 2.58/1.33  Simplification rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Subsume      : 8
% 2.58/1.33  #Demod        : 82
% 2.58/1.33  #Tautology    : 59
% 2.58/1.33  #SimpNegUnit  : 0
% 2.58/1.33  #BackRed      : 23
% 2.58/1.33  
% 2.58/1.33  #Partial instantiations: 0
% 2.58/1.33  #Strategies tried      : 1
% 2.58/1.33  
% 2.58/1.33  Timing (in seconds)
% 2.58/1.33  ----------------------
% 2.58/1.33  Preprocessing        : 0.32
% 2.58/1.33  Parsing              : 0.17
% 2.58/1.33  CNF conversion       : 0.02
% 2.58/1.33  Main loop            : 0.25
% 2.58/1.33  Inferencing          : 0.09
% 2.58/1.33  Reduction            : 0.08
% 2.58/1.33  Demodulation         : 0.06
% 2.58/1.33  BG Simplification    : 0.02
% 2.58/1.33  Subsumption          : 0.04
% 2.58/1.33  Abstraction          : 0.01
% 2.58/1.33  MUC search           : 0.00
% 2.58/1.33  Cooper               : 0.00
% 2.58/1.33  Total                : 0.61
% 2.58/1.33  Index Insertion      : 0.00
% 2.58/1.33  Index Deletion       : 0.00
% 2.58/1.33  Index Matching       : 0.00
% 2.58/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
