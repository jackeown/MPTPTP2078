%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:58 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 196 expanded)
%              Number of leaves         :   21 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 779 expanded)
%              Number of equality atoms :   16 (  71 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    ! [B_20,C_21,A_22] :
      ( k1_xboole_0 = B_20
      | v1_partfun1(C_21,A_22)
      | ~ v1_funct_2(C_21,A_22,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_20)))
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_34])).

tff(c_42,plain,(
    v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_31,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_28])).

tff(c_37,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_31])).

tff(c_41,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_14,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_43,plain,(
    ! [D_23,C_24,A_25,B_26] :
      ( D_23 = C_24
      | ~ r1_partfun1(C_24,D_23)
      | ~ v1_partfun1(D_23,A_25)
      | ~ v1_partfun1(C_24,A_25)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(D_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_45,plain,(
    ! [A_25,B_26] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_25)
      | ~ v1_partfun1('#skF_3',A_25)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_43])).

tff(c_48,plain,(
    ! [A_25,B_26] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_25)
      | ~ v1_partfun1('#skF_3',A_25)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_45])).

tff(c_61,plain,(
    ! [A_31,B_32] :
      ( ~ v1_partfun1('#skF_4',A_31)
      | ~ v1_partfun1('#skF_3',A_31)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_64,plain,
    ( ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42,c_41,c_64])).

tff(c_69,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_12,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_72,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_2,plain,(
    ! [D_7,A_1,B_2,C_3] :
      ( k1_funct_1(D_7,'#skF_1'(A_1,B_2,C_3,D_7)) != k1_funct_1(C_3,'#skF_1'(A_1,B_2,C_3,D_7))
      | r2_relset_1(A_1,B_2,C_3,D_7)
      | ~ m1_subset_1(D_7,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_7,A_1,B_2)
      | ~ v1_funct_1(D_7)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_relset_1(A_38,B_39,C_40,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ v1_funct_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ v1_funct_1(C_40) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_105,plain,
    ( r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_103])).

tff(c_108,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_105])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_108])).

tff(c_112,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6,plain,(
    ! [C_11,B_10] :
      ( v1_partfun1(C_11,k1_xboole_0)
      | ~ v1_funct_2(C_11,k1_xboole_0,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,(
    ! [C_41,B_42] :
      ( v1_partfun1(C_41,'#skF_2')
      | ~ v1_funct_2(C_41,'#skF_2',B_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_42)))
      | ~ v1_funct_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_111,c_111,c_6])).

tff(c_125,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_119])).

tff(c_131,plain,(
    v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_125])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_131])).

tff(c_135,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_134,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_143,plain,(
    ! [C_43,B_44] :
      ( v1_partfun1(C_43,'#skF_2')
      | ~ v1_funct_2(C_43,'#skF_2',B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_44)))
      | ~ v1_funct_1(C_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_134,c_134,c_6])).

tff(c_146,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_143])).

tff(c_152,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_146])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.11/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.11/1.24  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.11/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.24  
% 2.11/1.26  tff(f_97, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_2)).
% 2.11/1.26  tff(f_62, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.11/1.26  tff(f_79, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.11/1.26  tff(f_45, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 2.11/1.26  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_24, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_28, plain, (![B_20, C_21, A_22]: (k1_xboole_0=B_20 | v1_partfun1(C_21, A_22) | ~v1_funct_2(C_21, A_22, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_20))) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.11/1.26  tff(c_34, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_28])).
% 2.11/1.26  tff(c_40, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_34])).
% 2.11/1.26  tff(c_42, plain, (v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.11/1.26  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_18, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_31, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_28])).
% 2.11/1.26  tff(c_37, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_31])).
% 2.11/1.26  tff(c_41, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_37])).
% 2.11/1.26  tff(c_14, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_43, plain, (![D_23, C_24, A_25, B_26]: (D_23=C_24 | ~r1_partfun1(C_24, D_23) | ~v1_partfun1(D_23, A_25) | ~v1_partfun1(C_24, A_25) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(D_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.26  tff(c_45, plain, (![A_25, B_26]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_25) | ~v1_partfun1('#skF_3', A_25) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_43])).
% 2.11/1.26  tff(c_48, plain, (![A_25, B_26]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_25) | ~v1_partfun1('#skF_3', A_25) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_45])).
% 2.11/1.26  tff(c_61, plain, (![A_31, B_32]: (~v1_partfun1('#skF_4', A_31) | ~v1_partfun1('#skF_3', A_31) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(splitLeft, [status(thm)], [c_48])).
% 2.11/1.26  tff(c_64, plain, (~v1_partfun1('#skF_4', '#skF_2') | ~v1_partfun1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.11/1.26  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_42, c_41, c_64])).
% 2.11/1.26  tff(c_69, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 2.11/1.26  tff(c_12, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.11/1.26  tff(c_72, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12])).
% 2.11/1.26  tff(c_2, plain, (![D_7, A_1, B_2, C_3]: (k1_funct_1(D_7, '#skF_1'(A_1, B_2, C_3, D_7))!=k1_funct_1(C_3, '#skF_1'(A_1, B_2, C_3, D_7)) | r2_relset_1(A_1, B_2, C_3, D_7) | ~m1_subset_1(D_7, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_7, A_1, B_2) | ~v1_funct_1(D_7) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.26  tff(c_103, plain, (![A_38, B_39, C_40]: (r2_relset_1(A_38, B_39, C_40, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(C_40, A_38, B_39) | ~v1_funct_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(C_40, A_38, B_39) | ~v1_funct_1(C_40))), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 2.11/1.26  tff(c_105, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_103])).
% 2.11/1.26  tff(c_108, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_105])).
% 2.11/1.26  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_108])).
% 2.11/1.26  tff(c_112, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.11/1.26  tff(c_111, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 2.11/1.26  tff(c_6, plain, (![C_11, B_10]: (v1_partfun1(C_11, k1_xboole_0) | ~v1_funct_2(C_11, k1_xboole_0, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_10))) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.11/1.26  tff(c_119, plain, (![C_41, B_42]: (v1_partfun1(C_41, '#skF_2') | ~v1_funct_2(C_41, '#skF_2', B_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_42))) | ~v1_funct_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_111, c_111, c_6])).
% 2.11/1.26  tff(c_125, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_119])).
% 2.11/1.26  tff(c_131, plain, (v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_125])).
% 2.11/1.26  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_131])).
% 2.11/1.26  tff(c_135, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_37])).
% 2.11/1.26  tff(c_134, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_37])).
% 2.11/1.26  tff(c_143, plain, (![C_43, B_44]: (v1_partfun1(C_43, '#skF_2') | ~v1_funct_2(C_43, '#skF_2', B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_44))) | ~v1_funct_1(C_43))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_134, c_134, c_6])).
% 2.11/1.26  tff(c_146, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_143])).
% 2.11/1.26  tff(c_152, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_146])).
% 2.11/1.26  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_152])).
% 2.11/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  Inference rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Ref     : 1
% 2.11/1.26  #Sup     : 19
% 2.11/1.26  #Fact    : 0
% 2.11/1.26  #Define  : 0
% 2.11/1.26  #Split   : 4
% 2.11/1.26  #Chain   : 0
% 2.11/1.26  #Close   : 0
% 2.11/1.26  
% 2.11/1.26  Ordering : KBO
% 2.11/1.26  
% 2.11/1.26  Simplification rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Subsume      : 1
% 2.11/1.26  #Demod        : 46
% 2.11/1.26  #Tautology    : 12
% 2.11/1.26  #SimpNegUnit  : 4
% 2.11/1.26  #BackRed      : 10
% 2.11/1.26  
% 2.11/1.26  #Partial instantiations: 0
% 2.11/1.26  #Strategies tried      : 1
% 2.11/1.26  
% 2.11/1.26  Timing (in seconds)
% 2.11/1.26  ----------------------
% 2.11/1.26  Preprocessing        : 0.30
% 2.11/1.26  Parsing              : 0.16
% 2.11/1.26  CNF conversion       : 0.02
% 2.11/1.26  Main loop            : 0.18
% 2.11/1.26  Inferencing          : 0.07
% 2.11/1.26  Reduction            : 0.06
% 2.11/1.26  Demodulation         : 0.04
% 2.11/1.26  BG Simplification    : 0.01
% 2.11/1.26  Subsumption          : 0.03
% 2.11/1.26  Abstraction          : 0.01
% 2.11/1.26  MUC search           : 0.00
% 2.11/1.26  Cooper               : 0.00
% 2.11/1.26  Total                : 0.52
% 2.11/1.26  Index Insertion      : 0.00
% 2.11/1.26  Index Deletion       : 0.00
% 2.11/1.26  Index Matching       : 0.00
% 2.11/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
