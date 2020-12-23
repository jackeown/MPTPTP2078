%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:52 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 228 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 714 expanded)
%              Number of equality atoms :   14 (  95 expanded)
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

tff(f_115,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_92,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_246,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( r2_relset_1(A_80,B_81,C_82,C_82)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_270,plain,(
    ! [C_87] :
      ( r2_relset_1('#skF_3','#skF_4',C_87,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_246])).

tff(c_279,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_270])).

tff(c_163,plain,(
    ! [C_59,B_60,A_61] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(B_60,A_61)))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_175,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_177,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_178,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_partfun1(C_62,A_63)
      | ~ v1_funct_2(C_62,A_63,B_64)
      | ~ v1_funct_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | v1_xboole_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_188,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_195,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_188])).

tff(c_197,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_195])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_185,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_192,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_185])).

tff(c_196,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_192])).

tff(c_36,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_312,plain,(
    ! [D_93,C_94,A_95,B_96] :
      ( D_93 = C_94
      | ~ r1_partfun1(C_94,D_93)
      | ~ v1_partfun1(D_93,A_95)
      | ~ v1_partfun1(C_94,A_95)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(D_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_314,plain,(
    ! [A_95,B_96] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_95)
      | ~ v1_partfun1('#skF_5',A_95)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_312])).

tff(c_317,plain,(
    ! [A_95,B_96] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_95)
      | ~ v1_partfun1('#skF_5',A_95)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_314])).

tff(c_774,plain,(
    ! [A_152,B_153] :
      ( ~ v1_partfun1('#skF_6',A_152)
      | ~ v1_partfun1('#skF_5',A_152)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_786,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_44,c_774])).

tff(c_791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_197,c_196,c_786])).

tff(c_792,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_799,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_32])).

tff(c_809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_799])).

tff(c_810,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_811,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_73,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_42,B_43] :
      ( ~ v1_xboole_0(A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_97,plain,(
    ! [A_46,B_47] :
      ( ~ v1_xboole_0(A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_97,c_12])).

tff(c_114,plain,(
    ! [B_43,A_42] :
      ( B_43 = A_42
      | ~ v1_xboole_0(B_43)
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_83,c_101])).

tff(c_823,plain,(
    ! [A_154] :
      ( A_154 = '#skF_4'
      | ~ v1_xboole_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_811,c_114])).

tff(c_836,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_810,c_823])).

tff(c_176,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_163])).

tff(c_819,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_176])).

tff(c_833,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_819,c_823])).

tff(c_841,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_32])).

tff(c_883,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_841])).

tff(c_853,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_38])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( r2_relset_1(A_18,B_19,C_20,C_20)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_916,plain,(
    ! [C_162] :
      ( r2_relset_1('#skF_3','#skF_4',C_162,C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_853,c_24])).

tff(c_918,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_853,c_916])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_883,c_918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  
% 3.33/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.33/1.53  
% 3.33/1.53  %Foreground sorts:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Background operators:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Foreground operators:
% 3.33/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.33/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.33/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.33/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.53  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.33/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.53  
% 3.47/1.55  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.47/1.55  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.47/1.55  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.47/1.55  tff(f_75, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.47/1.55  tff(f_92, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.47/1.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.47/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.47/1.55  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/1.55  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_246, plain, (![A_80, B_81, C_82, D_83]: (r2_relset_1(A_80, B_81, C_82, C_82) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.55  tff(c_270, plain, (![C_87]: (r2_relset_1('#skF_3', '#skF_4', C_87, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_38, c_246])).
% 3.47/1.55  tff(c_279, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_270])).
% 3.47/1.55  tff(c_163, plain, (![C_59, B_60, A_61]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(B_60, A_61))) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.55  tff(c_175, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_163])).
% 3.47/1.55  tff(c_177, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_175])).
% 3.47/1.55  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_178, plain, (![C_62, A_63, B_64]: (v1_partfun1(C_62, A_63) | ~v1_funct_2(C_62, A_63, B_64) | ~v1_funct_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | v1_xboole_0(B_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.47/1.55  tff(c_188, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_178])).
% 3.47/1.55  tff(c_195, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_188])).
% 3.47/1.55  tff(c_197, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_177, c_195])).
% 3.47/1.55  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_185, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_178])).
% 3.47/1.55  tff(c_192, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_185])).
% 3.47/1.55  tff(c_196, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_177, c_192])).
% 3.47/1.55  tff(c_36, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_312, plain, (![D_93, C_94, A_95, B_96]: (D_93=C_94 | ~r1_partfun1(C_94, D_93) | ~v1_partfun1(D_93, A_95) | ~v1_partfun1(C_94, A_95) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(D_93) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.47/1.55  tff(c_314, plain, (![A_95, B_96]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_95) | ~v1_partfun1('#skF_5', A_95) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_312])).
% 3.47/1.55  tff(c_317, plain, (![A_95, B_96]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_95) | ~v1_partfun1('#skF_5', A_95) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_314])).
% 3.47/1.55  tff(c_774, plain, (![A_152, B_153]: (~v1_partfun1('#skF_6', A_152) | ~v1_partfun1('#skF_5', A_152) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(splitLeft, [status(thm)], [c_317])).
% 3.47/1.55  tff(c_786, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_44, c_774])).
% 3.47/1.55  tff(c_791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_197, c_196, c_786])).
% 3.47/1.55  tff(c_792, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_317])).
% 3.47/1.55  tff(c_32, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.55  tff(c_799, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_792, c_32])).
% 3.47/1.55  tff(c_809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_279, c_799])).
% 3.47/1.55  tff(c_810, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_175])).
% 3.47/1.55  tff(c_811, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_175])).
% 3.47/1.55  tff(c_73, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.55  tff(c_83, plain, (![A_42, B_43]: (~v1_xboole_0(A_42) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_73, c_2])).
% 3.47/1.55  tff(c_97, plain, (![A_46, B_47]: (~v1_xboole_0(A_46) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_73, c_2])).
% 3.47/1.55  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.47/1.55  tff(c_101, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_97, c_12])).
% 3.47/1.55  tff(c_114, plain, (![B_43, A_42]: (B_43=A_42 | ~v1_xboole_0(B_43) | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_83, c_101])).
% 3.47/1.55  tff(c_823, plain, (![A_154]: (A_154='#skF_4' | ~v1_xboole_0(A_154))), inference(resolution, [status(thm)], [c_811, c_114])).
% 3.47/1.55  tff(c_836, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_810, c_823])).
% 3.47/1.55  tff(c_176, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_163])).
% 3.47/1.55  tff(c_819, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_176])).
% 3.47/1.55  tff(c_833, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_819, c_823])).
% 3.47/1.55  tff(c_841, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_32])).
% 3.47/1.55  tff(c_883, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_836, c_841])).
% 3.47/1.55  tff(c_853, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_38])).
% 3.47/1.55  tff(c_24, plain, (![A_18, B_19, C_20, D_21]: (r2_relset_1(A_18, B_19, C_20, C_20) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.55  tff(c_916, plain, (![C_162]: (r2_relset_1('#skF_3', '#skF_4', C_162, C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_853, c_24])).
% 3.47/1.55  tff(c_918, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_853, c_916])).
% 3.47/1.55  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_883, c_918])).
% 3.47/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.55  
% 3.47/1.55  Inference rules
% 3.47/1.55  ----------------------
% 3.47/1.55  #Ref     : 0
% 3.47/1.55  #Sup     : 200
% 3.47/1.55  #Fact    : 0
% 3.47/1.55  #Define  : 0
% 3.47/1.55  #Split   : 8
% 3.47/1.55  #Chain   : 0
% 3.47/1.55  #Close   : 0
% 3.47/1.55  
% 3.47/1.55  Ordering : KBO
% 3.47/1.55  
% 3.47/1.55  Simplification rules
% 3.47/1.55  ----------------------
% 3.47/1.55  #Subsume      : 80
% 3.47/1.55  #Demod        : 84
% 3.47/1.55  #Tautology    : 43
% 3.47/1.55  #SimpNegUnit  : 9
% 3.47/1.55  #BackRed      : 24
% 3.47/1.55  
% 3.47/1.55  #Partial instantiations: 0
% 3.47/1.55  #Strategies tried      : 1
% 3.47/1.55  
% 3.47/1.55  Timing (in seconds)
% 3.47/1.55  ----------------------
% 3.47/1.55  Preprocessing        : 0.33
% 3.47/1.55  Parsing              : 0.18
% 3.47/1.55  CNF conversion       : 0.02
% 3.47/1.55  Main loop            : 0.42
% 3.47/1.55  Inferencing          : 0.15
% 3.47/1.55  Reduction            : 0.12
% 3.47/1.55  Demodulation         : 0.08
% 3.47/1.55  BG Simplification    : 0.02
% 3.47/1.55  Subsumption          : 0.10
% 3.47/1.55  Abstraction          : 0.02
% 3.47/1.55  MUC search           : 0.00
% 3.47/1.55  Cooper               : 0.00
% 3.47/1.55  Total                : 0.78
% 3.47/1.55  Index Insertion      : 0.00
% 3.47/1.55  Index Deletion       : 0.00
% 3.47/1.55  Index Matching       : 0.00
% 3.47/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
