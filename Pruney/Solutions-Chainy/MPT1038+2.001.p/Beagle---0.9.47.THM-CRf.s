%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:00 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   53 (  92 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 391 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_91,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_68,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_partfun1)).

tff(c_10,plain,(
    ~ r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    r1_partfun1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_29,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_partfun1(C_22,A_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_29])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_43,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_partfun1(C_25,A_26)
      | ~ v1_funct_2(C_25,A_26,B_27)
      | ~ v1_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | v1_xboole_0(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_43])).

tff(c_55,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_46])).

tff(c_56,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_55])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,(
    ! [D_30,B_29,E_28,A_32,C_31] :
      ( r1_partfun1(C_31,D_30)
      | ~ v1_partfun1(E_28,A_32)
      | ~ r1_partfun1(D_30,E_28)
      | ~ r1_partfun1(C_31,E_28)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_32,B_29)))
      | ~ v1_funct_1(E_28)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_32,B_29)))
      | ~ v1_funct_1(D_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_29)))
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_69,plain,(
    ! [C_31,A_32,B_29] :
      ( r1_partfun1(C_31,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_32)
      | ~ r1_partfun1(C_31,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_32,B_29)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_32,B_29)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_29)))
      | ~ v1_funct_1(C_31) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_78,plain,(
    ! [C_33,A_34,B_35] :
      ( r1_partfun1(C_33,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_34)
      | ~ r1_partfun1(C_33,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_69])).

tff(c_80,plain,(
    ! [C_33] :
      ( r1_partfun1(C_33,'#skF_3')
      | ~ v1_partfun1('#skF_4','#skF_1')
      | ~ r1_partfun1(C_33,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_33) ) ),
    inference(resolution,[status(thm)],[c_22,c_78])).

tff(c_84,plain,(
    ! [C_36] :
      ( r1_partfun1(C_36,'#skF_3')
      | ~ r1_partfun1(C_36,'#skF_4')
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56,c_80])).

tff(c_90,plain,
    ( r1_partfun1('#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_99,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14,c_90])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_99])).

tff(c_102,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_127,plain,(
    ! [C_43,E_40,A_44,D_42,B_41] :
      ( r1_partfun1(C_43,D_42)
      | ~ v1_partfun1(E_40,A_44)
      | ~ r1_partfun1(D_42,E_40)
      | ~ r1_partfun1(C_43,E_40)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(A_44,B_41)))
      | ~ v1_funct_1(E_40)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_41)))
      | ~ v1_funct_1(D_42)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_41)))
      | ~ v1_funct_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_129,plain,(
    ! [C_43,A_44,B_41] :
      ( r1_partfun1(C_43,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_44)
      | ~ r1_partfun1(C_43,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_44,B_41)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_44,B_41)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_41)))
      | ~ v1_funct_1(C_43) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_138,plain,(
    ! [C_45,A_46,B_47] :
      ( r1_partfun1(C_45,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_46)
      | ~ r1_partfun1(C_45,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1(C_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_129])).

tff(c_140,plain,(
    ! [C_45] :
      ( r1_partfun1(C_45,'#skF_3')
      | ~ v1_partfun1('#skF_4','#skF_1')
      | ~ r1_partfun1(C_45,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_45) ) ),
    inference(resolution,[status(thm)],[c_22,c_138])).

tff(c_144,plain,(
    ! [C_48] :
      ( r1_partfun1(C_48,'#skF_3')
      | ~ r1_partfun1(C_48,'#skF_4')
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_102,c_140])).

tff(c_150,plain,
    ( r1_partfun1('#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_144])).

tff(c_159,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14,c_150])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  %$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.18  
% 1.91/1.18  %Foreground sorts:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Background operators:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Foreground operators:
% 1.91/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.91/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.91/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.18  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.91/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.18  
% 1.91/1.20  tff(f_91, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r1_partfun1(B, D) & r1_partfun1(C, D)) => r1_partfun1(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_2)).
% 1.91/1.20  tff(f_32, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 1.91/1.20  tff(f_46, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 1.91/1.20  tff(f_68, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((r1_partfun1(C, E) & r1_partfun1(D, E)) & v1_partfun1(E, A)) => r1_partfun1(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_partfun1)).
% 1.91/1.20  tff(c_10, plain, (~r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_14, plain, (r1_partfun1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_29, plain, (![C_22, A_23, B_24]: (v1_partfun1(C_22, A_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.20  tff(c_39, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_29])).
% 1.91/1.20  tff(c_42, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_39])).
% 1.91/1.20  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_18, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_43, plain, (![C_25, A_26, B_27]: (v1_partfun1(C_25, A_26) | ~v1_funct_2(C_25, A_26, B_27) | ~v1_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | v1_xboole_0(B_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.20  tff(c_46, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_43])).
% 1.91/1.20  tff(c_55, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_46])).
% 1.91/1.20  tff(c_56, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_55])).
% 1.91/1.20  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_12, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.91/1.20  tff(c_67, plain, (![D_30, B_29, E_28, A_32, C_31]: (r1_partfun1(C_31, D_30) | ~v1_partfun1(E_28, A_32) | ~r1_partfun1(D_30, E_28) | ~r1_partfun1(C_31, E_28) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_32, B_29))) | ~v1_funct_1(E_28) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_32, B_29))) | ~v1_funct_1(D_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_29))) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.20  tff(c_69, plain, (![C_31, A_32, B_29]: (r1_partfun1(C_31, '#skF_3') | ~v1_partfun1('#skF_4', A_32) | ~r1_partfun1(C_31, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_32, B_29))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_32, B_29))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_29))) | ~v1_funct_1(C_31))), inference(resolution, [status(thm)], [c_12, c_67])).
% 1.91/1.20  tff(c_78, plain, (![C_33, A_34, B_35]: (r1_partfun1(C_33, '#skF_3') | ~v1_partfun1('#skF_4', A_34) | ~r1_partfun1(C_33, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_69])).
% 1.91/1.20  tff(c_80, plain, (![C_33]: (r1_partfun1(C_33, '#skF_3') | ~v1_partfun1('#skF_4', '#skF_1') | ~r1_partfun1(C_33, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_33))), inference(resolution, [status(thm)], [c_22, c_78])).
% 1.91/1.20  tff(c_84, plain, (![C_36]: (r1_partfun1(C_36, '#skF_3') | ~r1_partfun1(C_36, '#skF_4') | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56, c_80])).
% 1.91/1.20  tff(c_90, plain, (r1_partfun1('#skF_2', '#skF_3') | ~r1_partfun1('#skF_2', '#skF_4') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_84])).
% 1.91/1.20  tff(c_99, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14, c_90])).
% 1.91/1.20  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_99])).
% 1.91/1.20  tff(c_102, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_39])).
% 1.91/1.20  tff(c_127, plain, (![C_43, E_40, A_44, D_42, B_41]: (r1_partfun1(C_43, D_42) | ~v1_partfun1(E_40, A_44) | ~r1_partfun1(D_42, E_40) | ~r1_partfun1(C_43, E_40) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(A_44, B_41))) | ~v1_funct_1(E_40) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_41))) | ~v1_funct_1(D_42) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_41))) | ~v1_funct_1(C_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.20  tff(c_129, plain, (![C_43, A_44, B_41]: (r1_partfun1(C_43, '#skF_3') | ~v1_partfun1('#skF_4', A_44) | ~r1_partfun1(C_43, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_44, B_41))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_44, B_41))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_41))) | ~v1_funct_1(C_43))), inference(resolution, [status(thm)], [c_12, c_127])).
% 1.91/1.20  tff(c_138, plain, (![C_45, A_46, B_47]: (r1_partfun1(C_45, '#skF_3') | ~v1_partfun1('#skF_4', A_46) | ~r1_partfun1(C_45, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1(C_45))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_129])).
% 1.91/1.20  tff(c_140, plain, (![C_45]: (r1_partfun1(C_45, '#skF_3') | ~v1_partfun1('#skF_4', '#skF_1') | ~r1_partfun1(C_45, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_45))), inference(resolution, [status(thm)], [c_22, c_138])).
% 1.91/1.20  tff(c_144, plain, (![C_48]: (r1_partfun1(C_48, '#skF_3') | ~r1_partfun1(C_48, '#skF_4') | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(C_48))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_102, c_140])).
% 1.91/1.20  tff(c_150, plain, (r1_partfun1('#skF_2', '#skF_3') | ~r1_partfun1('#skF_2', '#skF_4') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_144])).
% 1.91/1.20  tff(c_159, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14, c_150])).
% 1.91/1.20  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_159])).
% 1.91/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 21
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 3
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 2
% 1.91/1.20  #Demod        : 31
% 1.91/1.20  #Tautology    : 4
% 1.91/1.20  #SimpNegUnit  : 5
% 1.91/1.20  #BackRed      : 0
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.27
% 1.91/1.20  Parsing              : 0.15
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.17
% 1.91/1.20  Inferencing          : 0.07
% 1.91/1.20  Reduction            : 0.05
% 1.91/1.20  Demodulation         : 0.04
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.02
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.47
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
