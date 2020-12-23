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
% DateTime   : Thu Dec  3 10:14:00 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 184 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 301 expanded)
%              Number of equality atoms :   27 (  92 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_45,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_115,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_45,c_115])).

tff(c_124,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124,c_4])).

tff(c_84,plain,(
    ! [A_28,B_29] : v1_xboole_0('#skF_1'(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_88,plain,(
    ! [A_28,B_29] : '#skF_1'(A_28,B_29) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_32,plain,(
    ! [A_19,B_20] : v1_relat_1('#skF_1'(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_32])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_143,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_22])).

tff(c_30,plain,(
    ! [A_19,B_20] : v4_relat_1('#skF_1'(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_99,plain,(
    ! [A_19] : v4_relat_1(k1_xboole_0,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_30])).

tff(c_134,plain,(
    ! [A_19] : v4_relat_1('#skF_4',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_99])).

tff(c_218,plain,(
    ! [B_48,A_49] :
      ( k7_relat_1(B_48,A_49) = B_48
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_221,plain,(
    ! [A_19] :
      ( k7_relat_1('#skF_4',A_19) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_218])).

tff(c_225,plain,(
    ! [A_50] : k7_relat_1('#skF_4',A_50) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_221])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_230,plain,(
    ! [A_50] :
      ( k9_relat_1('#skF_4',A_50) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_18])).

tff(c_235,plain,(
    ! [A_50] : k9_relat_1('#skF_4',A_50) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_143,c_230])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_141,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_12])).

tff(c_260,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_263,plain,(
    ! [A_59,B_60,D_62] : k7_relset_1(A_59,B_60,'#skF_4',D_62) = k9_relat_1('#skF_4',D_62) ),
    inference(resolution,[status(thm)],[c_141,c_260])).

tff(c_269,plain,(
    ! [A_59,B_60,D_62] : k7_relset_1(A_59,B_60,'#skF_4',D_62) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_263])).

tff(c_38,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_132,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_38])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:29:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.16  
% 1.95/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.95/1.17  
% 1.95/1.17  %Foreground sorts:
% 1.95/1.17  
% 1.95/1.17  
% 1.95/1.17  %Background operators:
% 1.95/1.17  
% 1.95/1.17  
% 1.95/1.17  %Foreground operators:
% 1.95/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.95/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.95/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.95/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.95/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.17  
% 2.28/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.18  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.28/1.18  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 2.28/1.18  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.28/1.18  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.28/1.18  tff(f_79, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 2.28/1.18  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.28/1.18  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.28/1.18  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.28/1.18  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.28/1.18  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.28/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.28/1.18  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.28/1.18  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.28/1.18  tff(c_45, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 2.28/1.18  tff(c_115, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.18  tff(c_118, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_115])).
% 2.28/1.18  tff(c_124, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_118])).
% 2.28/1.18  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.28/1.18  tff(c_130, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_124, c_4])).
% 2.28/1.18  tff(c_84, plain, (![A_28, B_29]: (v1_xboole_0('#skF_1'(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.18  tff(c_88, plain, (![A_28, B_29]: ('#skF_1'(A_28, B_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_4])).
% 2.28/1.18  tff(c_32, plain, (![A_19, B_20]: (v1_relat_1('#skF_1'(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.18  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_32])).
% 2.28/1.18  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90])).
% 2.28/1.18  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.18  tff(c_143, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_22])).
% 2.28/1.18  tff(c_30, plain, (![A_19, B_20]: (v4_relat_1('#skF_1'(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.18  tff(c_99, plain, (![A_19]: (v4_relat_1(k1_xboole_0, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_30])).
% 2.28/1.18  tff(c_134, plain, (![A_19]: (v4_relat_1('#skF_4', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_99])).
% 2.28/1.18  tff(c_218, plain, (![B_48, A_49]: (k7_relat_1(B_48, A_49)=B_48 | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.28/1.18  tff(c_221, plain, (![A_19]: (k7_relat_1('#skF_4', A_19)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_134, c_218])).
% 2.28/1.18  tff(c_225, plain, (![A_50]: (k7_relat_1('#skF_4', A_50)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_221])).
% 2.28/1.18  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.28/1.18  tff(c_230, plain, (![A_50]: (k9_relat_1('#skF_4', A_50)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_225, c_18])).
% 2.28/1.18  tff(c_235, plain, (![A_50]: (k9_relat_1('#skF_4', A_50)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_143, c_230])).
% 2.28/1.18  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.18  tff(c_141, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_12])).
% 2.28/1.18  tff(c_260, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.28/1.18  tff(c_263, plain, (![A_59, B_60, D_62]: (k7_relset_1(A_59, B_60, '#skF_4', D_62)=k9_relat_1('#skF_4', D_62))), inference(resolution, [status(thm)], [c_141, c_260])).
% 2.28/1.18  tff(c_269, plain, (![A_59, B_60, D_62]: (k7_relset_1(A_59, B_60, '#skF_4', D_62)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_263])).
% 2.28/1.18  tff(c_38, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.28/1.18  tff(c_132, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_38])).
% 2.28/1.18  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_132])).
% 2.28/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.18  
% 2.28/1.18  Inference rules
% 2.28/1.18  ----------------------
% 2.28/1.18  #Ref     : 0
% 2.28/1.18  #Sup     : 50
% 2.28/1.18  #Fact    : 0
% 2.28/1.18  #Define  : 0
% 2.28/1.18  #Split   : 0
% 2.28/1.18  #Chain   : 0
% 2.28/1.18  #Close   : 0
% 2.28/1.18  
% 2.28/1.18  Ordering : KBO
% 2.28/1.18  
% 2.28/1.18  Simplification rules
% 2.28/1.18  ----------------------
% 2.28/1.18  #Subsume      : 0
% 2.28/1.18  #Demod        : 42
% 2.28/1.18  #Tautology    : 45
% 2.28/1.18  #SimpNegUnit  : 0
% 2.28/1.18  #BackRed      : 18
% 2.28/1.18  
% 2.28/1.18  #Partial instantiations: 0
% 2.28/1.18  #Strategies tried      : 1
% 2.28/1.18  
% 2.28/1.18  Timing (in seconds)
% 2.28/1.18  ----------------------
% 2.28/1.19  Preprocessing        : 0.31
% 2.28/1.19  Parsing              : 0.17
% 2.28/1.19  CNF conversion       : 0.02
% 2.28/1.19  Main loop            : 0.17
% 2.28/1.19  Inferencing          : 0.06
% 2.28/1.19  Reduction            : 0.06
% 2.28/1.19  Demodulation         : 0.04
% 2.28/1.19  BG Simplification    : 0.01
% 2.28/1.19  Subsumption          : 0.02
% 2.28/1.19  Abstraction          : 0.01
% 2.28/1.19  MUC search           : 0.00
% 2.28/1.19  Cooper               : 0.00
% 2.28/1.19  Total                : 0.51
% 2.28/1.19  Index Insertion      : 0.00
% 2.28/1.19  Index Deletion       : 0.00
% 2.28/1.19  Index Matching       : 0.00
% 2.28/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
