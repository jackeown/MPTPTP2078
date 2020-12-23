%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 245 expanded)
%              Number of leaves         :   23 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 812 expanded)
%              Number of equality atoms :   13 ( 120 expanded)
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

tff(f_100,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_77,axiom,(
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

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_43,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( r2_relset_1(A_26,B_27,C_28,C_28)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [C_30] :
      ( r2_relset_1('#skF_1','#skF_2',C_30,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_43])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_33,plain,(
    ! [C_23,B_24,A_25] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_24,A_25)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_57,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_partfun1(C_31,A_32)
      | ~ v1_funct_2(C_31,A_32,B_33)
      | ~ v1_funct_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_66,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_60])).

tff(c_67,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_66])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_63,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_70,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_63])).

tff(c_71,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_70])).

tff(c_18,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    ! [D_34,C_35,A_36,B_37] :
      ( D_34 = C_35
      | ~ r1_partfun1(C_35,D_34)
      | ~ v1_partfun1(D_34,A_36)
      | ~ v1_partfun1(C_35,A_36)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(D_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    ! [A_36,B_37] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_77,plain,(
    ! [A_36,B_37] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_36)
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_74])).

tff(c_79,plain,(
    ! [A_38,B_39] :
      ( ~ v1_partfun1('#skF_4',A_38)
      | ~ v1_partfun1('#skF_3',A_38)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_82,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_67,c_71,c_82])).

tff(c_87,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_14,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_91,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_14])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_91])).

tff(c_102,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_41,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_110,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_41])).

tff(c_101,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_40] :
      ( A_40 = '#skF_3'
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_124,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_114])).

tff(c_125,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_102,c_114])).

tff(c_143,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_125])).

tff(c_131,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_14])).

tff(c_161,plain,(
    ~ r2_relset_1('#skF_1','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_131])).

tff(c_145,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_20])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_relset_1(A_7,B_8,C_9,C_9)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_171,plain,(
    ! [C_46] :
      ( r2_relset_1('#skF_1','#skF_4',C_46,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_145,c_6])).

tff(c_173,plain,(
    r2_relset_1('#skF_1','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_145,c_171])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.45/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.35  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.45/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.35  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.45/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.35  
% 2.45/1.38  tff(f_100, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.45/1.38  tff(f_46, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.45/1.38  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.45/1.38  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.45/1.38  tff(f_77, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.45/1.38  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.45/1.38  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_43, plain, (![A_26, B_27, C_28, D_29]: (r2_relset_1(A_26, B_27, C_28, C_28) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.45/1.38  tff(c_50, plain, (![C_30]: (r2_relset_1('#skF_1', '#skF_2', C_30, C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_26, c_43])).
% 2.45/1.38  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_50])).
% 2.45/1.38  tff(c_33, plain, (![C_23, B_24, A_25]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_24, A_25))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.45/1.38  tff(c_40, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_33])).
% 2.45/1.38  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.45/1.38  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_57, plain, (![C_31, A_32, B_33]: (v1_partfun1(C_31, A_32) | ~v1_funct_2(C_31, A_32, B_33) | ~v1_funct_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.45/1.38  tff(c_60, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_57])).
% 2.45/1.38  tff(c_66, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_60])).
% 2.45/1.38  tff(c_67, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_66])).
% 2.45/1.38  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_22, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_63, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_57])).
% 2.45/1.38  tff(c_70, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_63])).
% 2.45/1.38  tff(c_71, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_70])).
% 2.45/1.38  tff(c_18, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_72, plain, (![D_34, C_35, A_36, B_37]: (D_34=C_35 | ~r1_partfun1(C_35, D_34) | ~v1_partfun1(D_34, A_36) | ~v1_partfun1(C_35, A_36) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(D_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.45/1.38  tff(c_74, plain, (![A_36, B_37]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_36) | ~v1_partfun1('#skF_3', A_36) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_72])).
% 2.45/1.38  tff(c_77, plain, (![A_36, B_37]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_36) | ~v1_partfun1('#skF_3', A_36) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_74])).
% 2.45/1.38  tff(c_79, plain, (![A_38, B_39]: (~v1_partfun1('#skF_4', A_38) | ~v1_partfun1('#skF_3', A_38) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(splitLeft, [status(thm)], [c_77])).
% 2.45/1.38  tff(c_82, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.45/1.38  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_67, c_71, c_82])).
% 2.45/1.38  tff(c_87, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_77])).
% 2.45/1.38  tff(c_14, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.45/1.38  tff(c_91, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_14])).
% 2.45/1.38  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_91])).
% 2.45/1.38  tff(c_102, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.45/1.38  tff(c_41, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_33])).
% 2.45/1.38  tff(c_110, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_41])).
% 2.45/1.38  tff(c_101, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.45/1.38  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.38  tff(c_114, plain, (![A_40]: (A_40='#skF_3' | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_101, c_2])).
% 2.45/1.38  tff(c_124, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_110, c_114])).
% 2.45/1.38  tff(c_125, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_102, c_114])).
% 2.45/1.38  tff(c_143, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_125])).
% 2.45/1.38  tff(c_131, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_14])).
% 2.45/1.38  tff(c_161, plain, (~r2_relset_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_131])).
% 2.45/1.38  tff(c_145, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_20])).
% 2.45/1.38  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (r2_relset_1(A_7, B_8, C_9, C_9) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.45/1.38  tff(c_171, plain, (![C_46]: (r2_relset_1('#skF_1', '#skF_4', C_46, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(resolution, [status(thm)], [c_145, c_6])).
% 2.45/1.38  tff(c_173, plain, (r2_relset_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_145, c_171])).
% 2.45/1.38  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_173])).
% 2.45/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.38  
% 2.45/1.38  Inference rules
% 2.45/1.38  ----------------------
% 2.45/1.38  #Ref     : 0
% 2.45/1.38  #Sup     : 24
% 2.45/1.38  #Fact    : 0
% 2.45/1.38  #Define  : 0
% 2.45/1.38  #Split   : 3
% 2.45/1.38  #Chain   : 0
% 2.45/1.38  #Close   : 0
% 2.45/1.38  
% 2.45/1.38  Ordering : KBO
% 2.45/1.38  
% 2.45/1.38  Simplification rules
% 2.45/1.38  ----------------------
% 2.45/1.38  #Subsume      : 4
% 2.45/1.38  #Demod        : 43
% 2.45/1.38  #Tautology    : 16
% 2.45/1.38  #SimpNegUnit  : 3
% 2.45/1.38  #BackRed      : 18
% 2.45/1.38  
% 2.45/1.38  #Partial instantiations: 0
% 2.45/1.38  #Strategies tried      : 1
% 2.45/1.38  
% 2.45/1.38  Timing (in seconds)
% 2.45/1.38  ----------------------
% 2.60/1.38  Preprocessing        : 0.32
% 2.60/1.38  Parsing              : 0.18
% 2.60/1.38  CNF conversion       : 0.02
% 2.60/1.38  Main loop            : 0.21
% 2.60/1.38  Inferencing          : 0.07
% 2.60/1.38  Reduction            : 0.07
% 2.60/1.38  Demodulation         : 0.05
% 2.60/1.38  BG Simplification    : 0.01
% 2.60/1.38  Subsumption          : 0.03
% 2.60/1.38  Abstraction          : 0.01
% 2.60/1.38  MUC search           : 0.00
% 2.60/1.38  Cooper               : 0.00
% 2.60/1.38  Total                : 0.58
% 2.60/1.38  Index Insertion      : 0.00
% 2.60/1.38  Index Deletion       : 0.00
% 2.60/1.38  Index Matching       : 0.00
% 2.60/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
