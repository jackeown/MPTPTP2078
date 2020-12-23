%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:01 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 288 expanded)
%              Number of leaves         :   21 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 851 expanded)
%              Number of equality atoms :    9 (  74 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
               => ( ( r1_partfun1(B,D)
                    & r1_partfun1(C,D) )
                 => r1_partfun1(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ( ( r1_partfun1(C,E)
                  & r1_partfun1(D,E)
                  & v1_partfun1(E,A) )
               => r1_partfun1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_12,plain,(
    ~ r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    r1_partfun1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [C_24,B_25,A_26] :
      ( v1_xboole_0(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(B_25,A_26)))
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_45,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_partfun1(C_27,A_28)
      | ~ v1_funct_2(C_27,A_28,B_29)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_62,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_52])).

tff(c_63,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_62])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,(
    ! [D_30,C_34,B_32,A_33,E_31] :
      ( r1_partfun1(C_34,D_30)
      | ~ v1_partfun1(E_31,A_33)
      | ~ r1_partfun1(D_30,E_31)
      | ~ r1_partfun1(C_34,E_31)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_33,B_32)))
      | ~ v1_funct_1(E_31)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_33,B_32)))
      | ~ v1_funct_1(D_30)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_33,B_32)))
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_72,plain,(
    ! [C_34,A_33,B_32] :
      ( r1_partfun1(C_34,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_33)
      | ~ r1_partfun1(C_34,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_33,B_32)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_33,B_32)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_33,B_32)))
      | ~ v1_funct_1(C_34) ) ),
    inference(resolution,[status(thm)],[c_14,c_70])).

tff(c_81,plain,(
    ! [C_35,A_36,B_37] :
      ( r1_partfun1(C_35,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_36)
      | ~ r1_partfun1(C_35,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_72])).

tff(c_83,plain,(
    ! [C_35] :
      ( r1_partfun1(C_35,'#skF_3')
      | ~ v1_partfun1('#skF_4','#skF_1')
      | ~ r1_partfun1(C_35,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_87,plain,(
    ! [C_38] :
      ( r1_partfun1(C_38,'#skF_3')
      | ~ r1_partfun1(C_38,'#skF_4')
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_63,c_83])).

tff(c_90,plain,
    ( r1_partfun1('#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_99,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16,c_90])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_99])).

tff(c_103,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_43,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_137,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_43])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_102,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_126,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_138,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126])).

tff(c_131,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_2])).

tff(c_167,plain,(
    ! [A_47] :
      ( A_47 = '#skF_1'
      | ~ v1_xboole_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_131])).

tff(c_178,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_137,c_167])).

tff(c_44,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_32])).

tff(c_165,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44])).

tff(c_177,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_165,c_167])).

tff(c_145,plain,(
    ~ r1_partfun1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_182,plain,(
    ~ r1_partfun1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_145])).

tff(c_233,plain,(
    ~ r1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_178,c_182])).

tff(c_146,plain,(
    r1_partfun1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_16])).

tff(c_208,plain,(
    r1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_146])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.33  
% 2.03/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.33  %$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.30/1.33  
% 2.30/1.33  %Foreground sorts:
% 2.30/1.33  
% 2.30/1.33  
% 2.30/1.33  %Background operators:
% 2.30/1.33  
% 2.30/1.33  
% 2.30/1.33  %Foreground operators:
% 2.30/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.30/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.30/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.33  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.30/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.33  
% 2.30/1.35  tff(f_95, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r1_partfun1(B, D) & r1_partfun1(C, D)) => r1_partfun1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_2)).
% 2.30/1.35  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.30/1.35  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.30/1.35  tff(f_72, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((r1_partfun1(C, E) & r1_partfun1(D, E)) & v1_partfun1(E, A)) => r1_partfun1(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_partfun1)).
% 2.30/1.35  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.30/1.35  tff(c_12, plain, (~r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_16, plain, (r1_partfun1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_32, plain, (![C_24, B_25, A_26]: (v1_xboole_0(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(B_25, A_26))) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.30/1.35  tff(c_42, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_32])).
% 2.30/1.35  tff(c_45, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 2.30/1.35  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_20, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_46, plain, (![C_27, A_28, B_29]: (v1_partfun1(C_27, A_28) | ~v1_funct_2(C_27, A_28, B_29) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.35  tff(c_52, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_46])).
% 2.30/1.35  tff(c_62, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_52])).
% 2.30/1.35  tff(c_63, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_45, c_62])).
% 2.30/1.35  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_14, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.35  tff(c_70, plain, (![D_30, C_34, B_32, A_33, E_31]: (r1_partfun1(C_34, D_30) | ~v1_partfun1(E_31, A_33) | ~r1_partfun1(D_30, E_31) | ~r1_partfun1(C_34, E_31) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_33, B_32))) | ~v1_funct_1(E_31) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_33, B_32))) | ~v1_funct_1(D_30) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_33, B_32))) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.35  tff(c_72, plain, (![C_34, A_33, B_32]: (r1_partfun1(C_34, '#skF_3') | ~v1_partfun1('#skF_4', A_33) | ~r1_partfun1(C_34, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_33, B_32))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_33, B_32))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_33, B_32))) | ~v1_funct_1(C_34))), inference(resolution, [status(thm)], [c_14, c_70])).
% 2.30/1.35  tff(c_81, plain, (![C_35, A_36, B_37]: (r1_partfun1(C_35, '#skF_3') | ~v1_partfun1('#skF_4', A_36) | ~r1_partfun1(C_35, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_72])).
% 2.30/1.35  tff(c_83, plain, (![C_35]: (r1_partfun1(C_35, '#skF_3') | ~v1_partfun1('#skF_4', '#skF_1') | ~r1_partfun1(C_35, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_35))), inference(resolution, [status(thm)], [c_24, c_81])).
% 2.30/1.35  tff(c_87, plain, (![C_38]: (r1_partfun1(C_38, '#skF_3') | ~r1_partfun1(C_38, '#skF_4') | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_38))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_63, c_83])).
% 2.30/1.35  tff(c_90, plain, (r1_partfun1('#skF_2', '#skF_3') | ~r1_partfun1('#skF_2', '#skF_4') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.30/1.35  tff(c_99, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16, c_90])).
% 2.30/1.35  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_99])).
% 2.30/1.35  tff(c_103, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 2.30/1.35  tff(c_43, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_32])).
% 2.30/1.35  tff(c_137, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_43])).
% 2.30/1.35  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.35  tff(c_130, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_103, c_2])).
% 2.30/1.35  tff(c_102, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.30/1.35  tff(c_126, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_102, c_2])).
% 2.30/1.35  tff(c_138, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126])).
% 2.30/1.35  tff(c_131, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_2])).
% 2.30/1.35  tff(c_167, plain, (![A_47]: (A_47='#skF_1' | ~v1_xboole_0(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_131])).
% 2.30/1.35  tff(c_178, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_137, c_167])).
% 2.30/1.35  tff(c_44, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_32])).
% 2.30/1.35  tff(c_165, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44])).
% 2.30/1.35  tff(c_177, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_165, c_167])).
% 2.30/1.35  tff(c_145, plain, (~r1_partfun1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_12])).
% 2.30/1.35  tff(c_182, plain, (~r1_partfun1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_145])).
% 2.30/1.35  tff(c_233, plain, (~r1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_178, c_182])).
% 2.30/1.35  tff(c_146, plain, (r1_partfun1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_16])).
% 2.30/1.35  tff(c_208, plain, (r1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_146])).
% 2.30/1.35  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_208])).
% 2.30/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.35  
% 2.30/1.35  Inference rules
% 2.30/1.35  ----------------------
% 2.30/1.35  #Ref     : 0
% 2.30/1.35  #Sup     : 40
% 2.30/1.35  #Fact    : 0
% 2.30/1.35  #Define  : 0
% 2.30/1.35  #Split   : 3
% 2.30/1.35  #Chain   : 0
% 2.30/1.35  #Close   : 0
% 2.30/1.35  
% 2.30/1.35  Ordering : KBO
% 2.30/1.35  
% 2.30/1.35  Simplification rules
% 2.30/1.35  ----------------------
% 2.30/1.35  #Subsume      : 2
% 2.30/1.35  #Demod        : 64
% 2.30/1.35  #Tautology    : 27
% 2.30/1.35  #SimpNegUnit  : 5
% 2.30/1.35  #BackRed      : 22
% 2.30/1.35  
% 2.30/1.35  #Partial instantiations: 0
% 2.30/1.35  #Strategies tried      : 1
% 2.30/1.35  
% 2.30/1.35  Timing (in seconds)
% 2.30/1.35  ----------------------
% 2.30/1.36  Preprocessing        : 0.32
% 2.30/1.36  Parsing              : 0.18
% 2.30/1.36  CNF conversion       : 0.02
% 2.30/1.36  Main loop            : 0.23
% 2.30/1.36  Inferencing          : 0.09
% 2.30/1.36  Reduction            : 0.07
% 2.30/1.36  Demodulation         : 0.05
% 2.30/1.36  BG Simplification    : 0.01
% 2.30/1.36  Subsumption          : 0.03
% 2.30/1.36  Abstraction          : 0.01
% 2.30/1.36  MUC search           : 0.00
% 2.30/1.36  Cooper               : 0.00
% 2.30/1.36  Total                : 0.59
% 2.30/1.36  Index Insertion      : 0.00
% 2.30/1.36  Index Deletion       : 0.00
% 2.30/1.36  Index Matching       : 0.00
% 2.30/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
