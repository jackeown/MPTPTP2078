%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:45 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   62 (  76 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 148 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_57,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k1_relat_1(B_41),A_42)
      | ~ v4_relat_1(B_41,A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [B_57,A_58] :
      ( k2_xboole_0(k1_relat_1(B_57),A_58) = A_58
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [B_63,C_64,A_65] :
      ( r1_tarski(k1_relat_1(B_63),C_64)
      | ~ r1_tarski(A_65,C_64)
      | ~ v4_relat_1(B_63,A_65)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_137,plain,(
    ! [B_66] :
      ( r1_tarski(k1_relat_1(B_66),'#skF_4')
      | ~ v4_relat_1(B_66,'#skF_2')
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_26,c_127])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_160,plain,(
    ! [B_68] :
      ( k7_relat_1(B_68,'#skF_4') = B_68
      | ~ v4_relat_1(B_68,'#skF_2')
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_137,c_10])).

tff(c_163,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_61,c_160])).

tff(c_166,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_163])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_82,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k2_partfun1(A_50,B_51,C_52,D_53) = k7_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    ! [D_53] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_53) = k7_relat_1('#skF_5',D_53)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_87,plain,(
    ! [D_53] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_53) = k7_relat_1('#skF_5',D_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_84])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_88,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_24])).

tff(c_173,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_88])).

tff(c_30,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [D_26,A_20,B_21,C_22] :
      ( k1_funct_1(D_26,'#skF_1'(A_20,B_21,C_22,D_26)) != k1_funct_1(C_22,'#skF_1'(A_20,B_21,C_22,D_26))
      | r2_relset_1(A_20,B_21,C_22,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_26,A_20,B_21)
      | ~ v1_funct_1(D_26)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_344,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_relset_1(A_96,B_97,C_98,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20])).

tff(c_346,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_344])).

tff(c_349,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_346])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.42  
% 2.55/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.43  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.55/1.43  
% 2.55/1.43  %Foreground sorts:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Background operators:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Foreground operators:
% 2.55/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.55/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.55/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.55/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.43  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.55/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.55/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.55/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.43  
% 2.55/1.44  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.55/1.44  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.44  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.55/1.44  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.55/1.44  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.55/1.44  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.55/1.44  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.55/1.44  tff(f_61, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.55/1.44  tff(f_81, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 2.55/1.44  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.44  tff(c_38, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.44  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_38])).
% 2.55/1.44  tff(c_57, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.44  tff(c_61, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_57])).
% 2.55/1.44  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.44  tff(c_62, plain, (![B_41, A_42]: (r1_tarski(k1_relat_1(B_41), A_42) | ~v4_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.44  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.44  tff(c_109, plain, (![B_57, A_58]: (k2_xboole_0(k1_relat_1(B_57), A_58)=A_58 | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_62, c_4])).
% 2.55/1.44  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.44  tff(c_127, plain, (![B_63, C_64, A_65]: (r1_tarski(k1_relat_1(B_63), C_64) | ~r1_tarski(A_65, C_64) | ~v4_relat_1(B_63, A_65) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_109, c_2])).
% 2.55/1.44  tff(c_137, plain, (![B_66]: (r1_tarski(k1_relat_1(B_66), '#skF_4') | ~v4_relat_1(B_66, '#skF_2') | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_26, c_127])).
% 2.55/1.44  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.44  tff(c_160, plain, (![B_68]: (k7_relat_1(B_68, '#skF_4')=B_68 | ~v4_relat_1(B_68, '#skF_2') | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_137, c_10])).
% 2.55/1.44  tff(c_163, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_61, c_160])).
% 2.55/1.44  tff(c_166, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_163])).
% 2.55/1.44  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.44  tff(c_82, plain, (![A_50, B_51, C_52, D_53]: (k2_partfun1(A_50, B_51, C_52, D_53)=k7_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.44  tff(c_84, plain, (![D_53]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_53)=k7_relat_1('#skF_5', D_53) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_82])).
% 2.55/1.44  tff(c_87, plain, (![D_53]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_53)=k7_relat_1('#skF_5', D_53))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_84])).
% 2.55/1.44  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.44  tff(c_88, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_24])).
% 2.55/1.44  tff(c_173, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_88])).
% 2.55/1.44  tff(c_30, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.44  tff(c_20, plain, (![D_26, A_20, B_21, C_22]: (k1_funct_1(D_26, '#skF_1'(A_20, B_21, C_22, D_26))!=k1_funct_1(C_22, '#skF_1'(A_20, B_21, C_22, D_26)) | r2_relset_1(A_20, B_21, C_22, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(D_26, A_20, B_21) | ~v1_funct_1(D_26) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.55/1.44  tff(c_344, plain, (![A_96, B_97, C_98]: (r2_relset_1(A_96, B_97, C_98, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98))), inference(reflexivity, [status(thm), theory('equality')], [c_20])).
% 2.55/1.44  tff(c_346, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_344])).
% 2.55/1.44  tff(c_349, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_346])).
% 2.55/1.44  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_349])).
% 2.55/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.44  
% 2.55/1.44  Inference rules
% 2.55/1.44  ----------------------
% 2.55/1.44  #Ref     : 1
% 2.55/1.44  #Sup     : 64
% 2.55/1.44  #Fact    : 0
% 2.55/1.44  #Define  : 0
% 2.55/1.44  #Split   : 2
% 2.55/1.44  #Chain   : 0
% 2.55/1.44  #Close   : 0
% 2.55/1.44  
% 2.55/1.44  Ordering : KBO
% 2.55/1.44  
% 2.55/1.44  Simplification rules
% 2.55/1.44  ----------------------
% 2.55/1.44  #Subsume      : 7
% 2.55/1.44  #Demod        : 30
% 2.55/1.44  #Tautology    : 24
% 2.55/1.44  #SimpNegUnit  : 2
% 2.55/1.44  #BackRed      : 2
% 2.55/1.44  
% 2.55/1.44  #Partial instantiations: 0
% 2.55/1.44  #Strategies tried      : 1
% 2.55/1.44  
% 2.55/1.44  Timing (in seconds)
% 2.55/1.44  ----------------------
% 2.55/1.44  Preprocessing        : 0.40
% 2.55/1.44  Parsing              : 0.24
% 2.55/1.44  CNF conversion       : 0.02
% 2.55/1.44  Main loop            : 0.27
% 2.55/1.44  Inferencing          : 0.11
% 2.55/1.44  Reduction            : 0.07
% 2.55/1.44  Demodulation         : 0.05
% 2.55/1.44  BG Simplification    : 0.02
% 2.55/1.44  Subsumption          : 0.06
% 2.55/1.44  Abstraction          : 0.02
% 2.55/1.44  MUC search           : 0.00
% 2.55/1.44  Cooper               : 0.00
% 2.55/1.44  Total                : 0.70
% 2.55/1.44  Index Insertion      : 0.00
% 2.55/1.44  Index Deletion       : 0.00
% 2.55/1.44  Index Matching       : 0.00
% 2.55/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
