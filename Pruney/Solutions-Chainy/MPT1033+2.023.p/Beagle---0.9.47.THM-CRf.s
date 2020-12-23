%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 300 expanded)
%              Number of leaves         :   23 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 974 expanded)
%              Number of equality atoms :   14 ( 147 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_45,plain,(
    ! [A_26,B_27,D_28] :
      ( r2_relset_1(A_26,B_27,D_28,D_28)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_35,plain,(
    ! [C_23,B_24,A_25] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_24,A_25)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_partfun1(C_29,A_30)
      | ~ v1_funct_2(C_29,A_30,B_31)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_65,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_58])).

tff(c_66,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_65])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_55,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_61,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_55])).

tff(c_62,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_61])).

tff(c_20,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,(
    ! [D_36,C_37,A_38,B_39] :
      ( D_36 = C_37
      | ~ r1_partfun1(C_37,D_36)
      | ~ v1_partfun1(D_36,A_38)
      | ~ v1_partfun1(C_37,A_38)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(D_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    ! [A_38,B_39] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_38)
      | ~ v1_partfun1('#skF_3',A_38)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_85,plain,(
    ! [A_38,B_39] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_38)
      | ~ v1_partfun1('#skF_3',A_38)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_82])).

tff(c_87,plain,(
    ! [A_40,B_41] :
      ( ~ v1_partfun1('#skF_4',A_40)
      | ~ v1_partfun1('#skF_3',A_40)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_90,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66,c_62,c_90])).

tff(c_95,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_16,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_99,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_16])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_99])).

tff(c_109,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_110,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ! [A_42] :
      ( A_42 = '#skF_2'
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_135,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_109,c_122])).

tff(c_43,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_35])).

tff(c_118,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_43])).

tff(c_132,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_118,c_122])).

tff(c_149,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_132])).

tff(c_140,plain,(
    ~ r2_relset_1('#skF_1','#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_16])).

tff(c_175,plain,(
    ~ r2_relset_1('#skF_1','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_149,c_140])).

tff(c_139,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_28])).

tff(c_176,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_149,c_139])).

tff(c_6,plain,(
    ! [A_7,B_8,D_10] :
      ( r2_relset_1(A_7,B_8,D_10,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_178,plain,(
    r2_relset_1('#skF_1','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_6])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.09/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.09/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.28  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.09/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.28  
% 2.09/1.30  tff(f_102, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.09/1.30  tff(f_48, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.09/1.30  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.09/1.30  tff(f_62, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.09/1.30  tff(f_79, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.09/1.30  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.09/1.30  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_45, plain, (![A_26, B_27, D_28]: (r2_relset_1(A_26, B_27, D_28, D_28) | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.30  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_45])).
% 2.09/1.30  tff(c_35, plain, (![C_23, B_24, A_25]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_24, A_25))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.30  tff(c_42, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_35])).
% 2.09/1.30  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.09/1.30  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_30, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_52, plain, (![C_29, A_30, B_31]: (v1_partfun1(C_29, A_30) | ~v1_funct_2(C_29, A_30, B_31) | ~v1_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.30  tff(c_58, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.09/1.30  tff(c_65, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_58])).
% 2.09/1.30  tff(c_66, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_65])).
% 2.09/1.30  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_55, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_52])).
% 2.09/1.30  tff(c_61, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_55])).
% 2.09/1.30  tff(c_62, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_61])).
% 2.09/1.30  tff(c_20, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_80, plain, (![D_36, C_37, A_38, B_39]: (D_36=C_37 | ~r1_partfun1(C_37, D_36) | ~v1_partfun1(D_36, A_38) | ~v1_partfun1(C_37, A_38) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(D_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.09/1.30  tff(c_82, plain, (![A_38, B_39]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_38) | ~v1_partfun1('#skF_3', A_38) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_80])).
% 2.09/1.30  tff(c_85, plain, (![A_38, B_39]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_38) | ~v1_partfun1('#skF_3', A_38) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_82])).
% 2.09/1.30  tff(c_87, plain, (![A_40, B_41]: (~v1_partfun1('#skF_4', A_40) | ~v1_partfun1('#skF_3', A_40) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(splitLeft, [status(thm)], [c_85])).
% 2.09/1.30  tff(c_90, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.09/1.30  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_66, c_62, c_90])).
% 2.09/1.30  tff(c_95, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_85])).
% 2.09/1.30  tff(c_16, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.09/1.30  tff(c_99, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_16])).
% 2.09/1.30  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_99])).
% 2.09/1.30  tff(c_109, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.09/1.30  tff(c_110, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.09/1.30  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.30  tff(c_122, plain, (![A_42]: (A_42='#skF_2' | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.09/1.30  tff(c_135, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_109, c_122])).
% 2.09/1.30  tff(c_43, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_35])).
% 2.09/1.30  tff(c_118, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_43])).
% 2.09/1.30  tff(c_132, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_118, c_122])).
% 2.09/1.30  tff(c_149, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_132])).
% 2.09/1.30  tff(c_140, plain, (~r2_relset_1('#skF_1', '#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_16])).
% 2.09/1.30  tff(c_175, plain, (~r2_relset_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_149, c_140])).
% 2.09/1.30  tff(c_139, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_28])).
% 2.09/1.30  tff(c_176, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_149, c_139])).
% 2.09/1.30  tff(c_6, plain, (![A_7, B_8, D_10]: (r2_relset_1(A_7, B_8, D_10, D_10) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.30  tff(c_178, plain, (r2_relset_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_176, c_6])).
% 2.09/1.30  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_178])).
% 2.09/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  Inference rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Ref     : 0
% 2.09/1.30  #Sup     : 25
% 2.09/1.30  #Fact    : 0
% 2.09/1.30  #Define  : 0
% 2.09/1.30  #Split   : 3
% 2.09/1.30  #Chain   : 0
% 2.09/1.30  #Close   : 0
% 2.09/1.30  
% 2.09/1.30  Ordering : KBO
% 2.09/1.30  
% 2.09/1.30  Simplification rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Subsume      : 3
% 2.09/1.30  #Demod        : 50
% 2.09/1.30  #Tautology    : 18
% 2.09/1.30  #SimpNegUnit  : 3
% 2.09/1.30  #BackRed      : 19
% 2.09/1.30  
% 2.09/1.30  #Partial instantiations: 0
% 2.09/1.30  #Strategies tried      : 1
% 2.09/1.30  
% 2.09/1.30  Timing (in seconds)
% 2.09/1.30  ----------------------
% 2.09/1.30  Preprocessing        : 0.32
% 2.09/1.30  Parsing              : 0.17
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.17
% 2.09/1.30  Inferencing          : 0.06
% 2.09/1.30  Reduction            : 0.06
% 2.09/1.30  Demodulation         : 0.04
% 2.09/1.30  BG Simplification    : 0.01
% 2.09/1.30  Subsumption          : 0.02
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.53
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
