%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:59 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 156 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :   73 ( 243 expanded)
%              Number of equality atoms :   27 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_41,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_100,plain,(
    ! [C_34] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_110,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_100])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_111,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_41,c_111])).

tff(c_122,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_126,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_126,c_22])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,(
    ! [A_43] : m1_subset_1('#skF_3',k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_12])).

tff(c_30,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_212,plain,(
    ! [A_18] : v4_relat_1('#skF_3',A_18) ),
    inference(resolution,[status(thm)],[c_200,c_30])).

tff(c_278,plain,(
    ! [B_59,A_60] :
      ( k7_relat_1(B_59,A_60) = B_59
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_281,plain,(
    ! [A_18] :
      ( k7_relat_1('#skF_3',A_18) = '#skF_3'
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_212,c_278])).

tff(c_285,plain,(
    ! [A_61] : k7_relat_1('#skF_3',A_61) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_281])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_290,plain,(
    ! [A_61] :
      ( k9_relat_1('#skF_3',A_61) = k2_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_18])).

tff(c_295,plain,(
    ! [A_61] : k9_relat_1('#skF_3',A_61) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_137,c_290])).

tff(c_133,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_12])).

tff(c_309,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( k7_relset_1(A_68,B_69,C_70,D_71) = k9_relat_1(C_70,D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_312,plain,(
    ! [A_68,B_69,D_71] : k7_relset_1(A_68,B_69,'#skF_3',D_71) = k9_relat_1('#skF_3',D_71) ),
    inference(resolution,[status(thm)],[c_133,c_309])).

tff(c_318,plain,(
    ! [A_68,B_69,D_71] : k7_relset_1(A_68,B_69,'#skF_3',D_71) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_312])).

tff(c_34,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_131,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_126,c_34])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:07:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.06/1.30  
% 2.06/1.30  %Foreground sorts:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Background operators:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Foreground operators:
% 2.06/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.06/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.06/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.06/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.30  
% 2.06/1.31  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.06/1.31  tff(f_87, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_2)).
% 2.06/1.31  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.06/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.31  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.06/1.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.06/1.31  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.06/1.31  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.06/1.31  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.06/1.31  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.06/1.31  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.06/1.31  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.06/1.31  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.31  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.06/1.31  tff(c_41, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 2.06/1.31  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.31  tff(c_90, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.06/1.31  tff(c_100, plain, (![C_34]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 2.06/1.31  tff(c_110, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_41, c_100])).
% 2.06/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.06/1.31  tff(c_111, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.31  tff(c_117, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_41, c_111])).
% 2.06/1.31  tff(c_122, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_117])).
% 2.06/1.31  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.06/1.31  tff(c_126, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_122, c_4])).
% 2.06/1.31  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.31  tff(c_137, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_126, c_22])).
% 2.06/1.31  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.31  tff(c_200, plain, (![A_43]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_12])).
% 2.06/1.31  tff(c_30, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.31  tff(c_212, plain, (![A_18]: (v4_relat_1('#skF_3', A_18))), inference(resolution, [status(thm)], [c_200, c_30])).
% 2.06/1.31  tff(c_278, plain, (![B_59, A_60]: (k7_relat_1(B_59, A_60)=B_59 | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.31  tff(c_281, plain, (![A_18]: (k7_relat_1('#skF_3', A_18)='#skF_3' | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_212, c_278])).
% 2.06/1.31  tff(c_285, plain, (![A_61]: (k7_relat_1('#skF_3', A_61)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_281])).
% 2.06/1.31  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.31  tff(c_290, plain, (![A_61]: (k9_relat_1('#skF_3', A_61)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_18])).
% 2.06/1.31  tff(c_295, plain, (![A_61]: (k9_relat_1('#skF_3', A_61)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_137, c_290])).
% 2.06/1.31  tff(c_133, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_12])).
% 2.06/1.31  tff(c_309, plain, (![A_68, B_69, C_70, D_71]: (k7_relset_1(A_68, B_69, C_70, D_71)=k9_relat_1(C_70, D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.31  tff(c_312, plain, (![A_68, B_69, D_71]: (k7_relset_1(A_68, B_69, '#skF_3', D_71)=k9_relat_1('#skF_3', D_71))), inference(resolution, [status(thm)], [c_133, c_309])).
% 2.06/1.31  tff(c_318, plain, (![A_68, B_69, D_71]: (k7_relset_1(A_68, B_69, '#skF_3', D_71)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_312])).
% 2.06/1.31  tff(c_34, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.06/1.31  tff(c_131, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_126, c_34])).
% 2.06/1.31  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_131])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 63
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 0
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 5
% 2.06/1.31  #Demod        : 41
% 2.06/1.31  #Tautology    : 46
% 2.06/1.31  #SimpNegUnit  : 0
% 2.06/1.31  #BackRed      : 14
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.32  Preprocessing        : 0.37
% 2.06/1.32  Parsing              : 0.20
% 2.06/1.32  CNF conversion       : 0.02
% 2.06/1.32  Main loop            : 0.18
% 2.06/1.32  Inferencing          : 0.07
% 2.06/1.32  Reduction            : 0.06
% 2.06/1.32  Demodulation         : 0.04
% 2.06/1.32  BG Simplification    : 0.01
% 2.06/1.32  Subsumption          : 0.03
% 2.06/1.32  Abstraction          : 0.01
% 2.06/1.32  MUC search           : 0.00
% 2.06/1.32  Cooper               : 0.00
% 2.06/1.32  Total                : 0.58
% 2.06/1.32  Index Insertion      : 0.00
% 2.06/1.32  Index Deletion       : 0.00
% 2.06/1.32  Index Matching       : 0.00
% 2.06/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
