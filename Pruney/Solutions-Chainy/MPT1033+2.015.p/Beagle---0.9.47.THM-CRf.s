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
% DateTime   : Thu Dec  3 10:16:52 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 193 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 610 expanded)
%              Number of equality atoms :   15 (  83 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_179,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_189,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_179])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_164,plain,(
    ! [C_59,B_60,A_61] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(B_60,A_61)))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_176,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_164])).

tff(c_178,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_209,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_partfun1(C_68,A_69)
      | ~ v1_funct_2(C_68,A_69,B_70)
      | ~ v1_funct_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | v1_xboole_0(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_216,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_209])).

tff(c_223,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_216])).

tff(c_224,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_223])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_219,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_209])).

tff(c_227,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_219])).

tff(c_228,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_227])).

tff(c_38,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_285,plain,(
    ! [D_92,C_93,A_94,B_95] :
      ( D_92 = C_93
      | ~ r1_partfun1(C_93,D_92)
      | ~ v1_partfun1(D_92,A_94)
      | ~ v1_partfun1(C_93,A_94)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1(D_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_287,plain,(
    ! [A_94,B_95] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_94)
      | ~ v1_partfun1('#skF_5',A_94)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_285])).

tff(c_290,plain,(
    ! [A_94,B_95] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_94)
      | ~ v1_partfun1('#skF_5',A_94)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_287])).

tff(c_633,plain,(
    ! [A_141,B_142] :
      ( ~ v1_partfun1('#skF_6',A_141)
      | ~ v1_partfun1('#skF_5',A_141)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_639,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_46,c_633])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_224,c_228,c_639])).

tff(c_645,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_653,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_34])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_653])).

tff(c_664,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_665,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_87,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_42,B_43] :
      ( ~ v1_xboole_0(A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_93,plain,(
    ! [A_44,B_45] :
      ( ~ v1_xboole_0(A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_114,plain,(
    ! [B_43,A_42] :
      ( B_43 = A_42
      | ~ v1_xboole_0(B_43)
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_91,c_101])).

tff(c_677,plain,(
    ! [A_143] :
      ( A_143 = '#skF_4'
      | ~ v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_665,c_114])).

tff(c_690,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_664,c_677])).

tff(c_177,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_164])).

tff(c_673,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_177])).

tff(c_687,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_673,c_677])).

tff(c_695,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_34])).

tff(c_737,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_695])).

tff(c_707,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_46])).

tff(c_24,plain,(
    ! [A_18,B_19,D_21] :
      ( r2_relset_1(A_18,B_19,D_21,D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_753,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_707,c_24])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_737,c_753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.49  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.21/1.49  
% 3.21/1.49  %Foreground sorts:
% 3.21/1.49  
% 3.21/1.49  
% 3.21/1.49  %Background operators:
% 3.21/1.49  
% 3.21/1.49  
% 3.21/1.49  %Foreground operators:
% 3.21/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.21/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.21/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.21/1.49  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.21/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.21/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.49  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.21/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.49  
% 3.21/1.51  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 3.21/1.51  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.21/1.51  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.21/1.51  tff(f_77, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.21/1.51  tff(f_94, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 3.21/1.51  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.21/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.21/1.51  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.51  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_179, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.21/1.51  tff(c_189, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_179])).
% 3.21/1.51  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_164, plain, (![C_59, B_60, A_61]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(B_60, A_61))) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.51  tff(c_176, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_164])).
% 3.21/1.51  tff(c_178, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_176])).
% 3.21/1.51  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_209, plain, (![C_68, A_69, B_70]: (v1_partfun1(C_68, A_69) | ~v1_funct_2(C_68, A_69, B_70) | ~v1_funct_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | v1_xboole_0(B_70))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.21/1.51  tff(c_216, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_209])).
% 3.21/1.51  tff(c_223, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_216])).
% 3.21/1.51  tff(c_224, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_178, c_223])).
% 3.21/1.51  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_219, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_209])).
% 3.21/1.51  tff(c_227, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_219])).
% 3.21/1.51  tff(c_228, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_178, c_227])).
% 3.21/1.51  tff(c_38, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_285, plain, (![D_92, C_93, A_94, B_95]: (D_92=C_93 | ~r1_partfun1(C_93, D_92) | ~v1_partfun1(D_92, A_94) | ~v1_partfun1(C_93, A_94) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1(D_92) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.51  tff(c_287, plain, (![A_94, B_95]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_94) | ~v1_partfun1('#skF_5', A_94) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_285])).
% 3.21/1.51  tff(c_290, plain, (![A_94, B_95]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_94) | ~v1_partfun1('#skF_5', A_94) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_287])).
% 3.21/1.51  tff(c_633, plain, (![A_141, B_142]: (~v1_partfun1('#skF_6', A_141) | ~v1_partfun1('#skF_5', A_141) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(splitLeft, [status(thm)], [c_290])).
% 3.21/1.51  tff(c_639, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_46, c_633])).
% 3.21/1.51  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_224, c_228, c_639])).
% 3.21/1.51  tff(c_645, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_290])).
% 3.21/1.51  tff(c_34, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.51  tff(c_653, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_34])).
% 3.21/1.51  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_653])).
% 3.21/1.51  tff(c_664, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_176])).
% 3.21/1.51  tff(c_665, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_176])).
% 3.21/1.51  tff(c_87, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.51  tff(c_91, plain, (![A_42, B_43]: (~v1_xboole_0(A_42) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_87, c_2])).
% 3.21/1.51  tff(c_93, plain, (![A_44, B_45]: (~v1_xboole_0(A_44) | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_87, c_2])).
% 3.21/1.51  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.21/1.51  tff(c_101, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_93, c_12])).
% 3.21/1.51  tff(c_114, plain, (![B_43, A_42]: (B_43=A_42 | ~v1_xboole_0(B_43) | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_91, c_101])).
% 3.21/1.51  tff(c_677, plain, (![A_143]: (A_143='#skF_4' | ~v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_665, c_114])).
% 3.21/1.51  tff(c_690, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_664, c_677])).
% 3.21/1.51  tff(c_177, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_164])).
% 3.21/1.51  tff(c_673, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_665, c_177])).
% 3.21/1.51  tff(c_687, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_673, c_677])).
% 3.21/1.51  tff(c_695, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_34])).
% 3.21/1.51  tff(c_737, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_690, c_695])).
% 3.21/1.51  tff(c_707, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_46])).
% 3.21/1.51  tff(c_24, plain, (![A_18, B_19, D_21]: (r2_relset_1(A_18, B_19, D_21, D_21) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.21/1.51  tff(c_753, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_707, c_24])).
% 3.21/1.51  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_737, c_753])).
% 3.21/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  Inference rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Ref     : 0
% 3.21/1.51  #Sup     : 150
% 3.21/1.51  #Fact    : 0
% 3.21/1.51  #Define  : 0
% 3.21/1.51  #Split   : 6
% 3.21/1.51  #Chain   : 0
% 3.21/1.51  #Close   : 0
% 3.21/1.51  
% 3.21/1.51  Ordering : KBO
% 3.21/1.51  
% 3.21/1.51  Simplification rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Subsume      : 56
% 3.21/1.51  #Demod        : 81
% 3.21/1.51  #Tautology    : 43
% 3.21/1.51  #SimpNegUnit  : 9
% 3.21/1.51  #BackRed      : 25
% 3.21/1.51  
% 3.21/1.51  #Partial instantiations: 0
% 3.21/1.51  #Strategies tried      : 1
% 3.21/1.51  
% 3.21/1.51  Timing (in seconds)
% 3.21/1.51  ----------------------
% 3.21/1.51  Preprocessing        : 0.34
% 3.21/1.51  Parsing              : 0.18
% 3.21/1.51  CNF conversion       : 0.02
% 3.21/1.51  Main loop            : 0.38
% 3.21/1.51  Inferencing          : 0.13
% 3.21/1.51  Reduction            : 0.11
% 3.21/1.51  Demodulation         : 0.07
% 3.21/1.51  BG Simplification    : 0.02
% 3.21/1.51  Subsumption          : 0.09
% 3.21/1.51  Abstraction          : 0.01
% 3.21/1.51  MUC search           : 0.00
% 3.21/1.51  Cooper               : 0.00
% 3.21/1.51  Total                : 0.75
% 3.21/1.51  Index Insertion      : 0.00
% 3.21/1.51  Index Deletion       : 0.00
% 3.21/1.51  Index Matching       : 0.00
% 3.21/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
