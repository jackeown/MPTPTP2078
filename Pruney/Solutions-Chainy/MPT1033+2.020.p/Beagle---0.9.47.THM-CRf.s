%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 281 expanded)
%              Number of leaves         :   29 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 856 expanded)
%              Number of equality atoms :   16 ( 106 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_95,axiom,(
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
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_167,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_relset_1(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_177,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_167])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_152,plain,(
    ! [C_60,B_61,A_62] :
      ( v1_xboole_0(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(B_61,A_62)))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_152])).

tff(c_166,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_178,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_188,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_196,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_188])).

tff(c_197,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_196])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_185,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_192,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_185])).

tff(c_193,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_192])).

tff(c_36,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_269,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r1_partfun1(C_90,D_89)
      | ~ v1_partfun1(D_89,A_91)
      | ~ v1_partfun1(C_90,A_91)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1(D_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_271,plain,(
    ! [A_91,B_92] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_91)
      | ~ v1_partfun1('#skF_4',A_91)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_269])).

tff(c_274,plain,(
    ! [A_91,B_92] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_91)
      | ~ v1_partfun1('#skF_4',A_91)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_271])).

tff(c_770,plain,(
    ! [A_162,B_163] :
      ( ~ v1_partfun1('#skF_5',A_162)
      | ~ v1_partfun1('#skF_4',A_162)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_776,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_38,c_770])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_197,c_193,c_776])).

tff(c_782,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_792,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_32])).

tff(c_802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_792])).

tff(c_804,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_165,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_152])).

tff(c_812,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_165])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [B_45,A_46,A_47] :
      ( ~ v1_xboole_0(B_45)
      | ~ r2_hidden(A_46,A_47)
      | ~ r1_tarski(A_47,B_45) ) ),
    inference(resolution,[status(thm)],[c_16,c_87])).

tff(c_102,plain,(
    ! [B_48,A_49,B_50] :
      ( ~ v1_xboole_0(B_48)
      | ~ r1_tarski(A_49,B_48)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_111,plain,(
    ! [B_7,B_50] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_112,plain,(
    ! [B_51,B_52] :
      ( ~ v1_xboole_0(B_51)
      | r1_tarski(B_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_123,plain,(
    ! [B_57,B_56] :
      ( B_57 = B_56
      | ~ r1_tarski(B_56,B_57)
      | ~ v1_xboole_0(B_57) ) ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_136,plain,(
    ! [B_7,B_50] :
      ( B_7 = B_50
      | ~ v1_xboole_0(B_50)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_111,c_123])).

tff(c_816,plain,(
    ! [B_164] :
      ( B_164 = '#skF_3'
      | ~ v1_xboole_0(B_164) ) ),
    inference(resolution,[status(thm)],[c_804,c_136])).

tff(c_826,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_812,c_816])).

tff(c_803,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_829,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_803,c_816])).

tff(c_848,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_829])).

tff(c_839,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_32])).

tff(c_872,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_839])).

tff(c_838,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_44])).

tff(c_22,plain,(
    ! [A_17,B_18,D_20] :
      ( r2_relset_1(A_17,B_18,D_20,D_20)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_899,plain,(
    r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_838,c_22])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_872,c_899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:21:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.49  
% 3.25/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.25/1.50  
% 3.25/1.50  %Foreground sorts:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Background operators:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Foreground operators:
% 3.25/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.25/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.50  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.25/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.50  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.25/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.50  
% 3.25/1.51  tff(f_118, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.25/1.51  tff(f_64, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.25/1.51  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.25/1.51  tff(f_78, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.25/1.51  tff(f_95, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.25/1.51  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.25/1.51  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.25/1.51  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.25/1.51  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_167, plain, (![A_63, B_64, D_65]: (r2_relset_1(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.25/1.51  tff(c_177, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_167])).
% 3.25/1.51  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_152, plain, (![C_60, B_61, A_62]: (v1_xboole_0(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(B_61, A_62))) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.25/1.51  tff(c_164, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_152])).
% 3.25/1.51  tff(c_166, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_164])).
% 3.25/1.51  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_178, plain, (![C_66, A_67, B_68]: (v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.25/1.51  tff(c_188, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_178])).
% 3.25/1.51  tff(c_196, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_188])).
% 3.25/1.51  tff(c_197, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_166, c_196])).
% 3.25/1.51  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_185, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_178])).
% 3.25/1.51  tff(c_192, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_185])).
% 3.25/1.51  tff(c_193, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_166, c_192])).
% 3.25/1.51  tff(c_36, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_269, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r1_partfun1(C_90, D_89) | ~v1_partfun1(D_89, A_91) | ~v1_partfun1(C_90, A_91) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1(D_89) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.25/1.51  tff(c_271, plain, (![A_91, B_92]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_91) | ~v1_partfun1('#skF_4', A_91) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_269])).
% 3.25/1.51  tff(c_274, plain, (![A_91, B_92]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_91) | ~v1_partfun1('#skF_4', A_91) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_271])).
% 3.25/1.51  tff(c_770, plain, (![A_162, B_163]: (~v1_partfun1('#skF_5', A_162) | ~v1_partfun1('#skF_4', A_162) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(splitLeft, [status(thm)], [c_274])).
% 3.25/1.51  tff(c_776, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_38, c_770])).
% 3.25/1.51  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_197, c_193, c_776])).
% 3.25/1.51  tff(c_782, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_274])).
% 3.25/1.51  tff(c_32, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.51  tff(c_792, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_32])).
% 3.25/1.51  tff(c_802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_792])).
% 3.25/1.51  tff(c_804, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_164])).
% 3.25/1.51  tff(c_165, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_152])).
% 3.25/1.51  tff(c_812, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_804, c_165])).
% 3.25/1.51  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.25/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.25/1.51  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.25/1.51  tff(c_87, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.25/1.51  tff(c_98, plain, (![B_45, A_46, A_47]: (~v1_xboole_0(B_45) | ~r2_hidden(A_46, A_47) | ~r1_tarski(A_47, B_45))), inference(resolution, [status(thm)], [c_16, c_87])).
% 3.25/1.51  tff(c_102, plain, (![B_48, A_49, B_50]: (~v1_xboole_0(B_48) | ~r1_tarski(A_49, B_48) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_98])).
% 3.25/1.51  tff(c_111, plain, (![B_7, B_50]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_50))), inference(resolution, [status(thm)], [c_12, c_102])).
% 3.25/1.51  tff(c_112, plain, (![B_51, B_52]: (~v1_xboole_0(B_51) | r1_tarski(B_51, B_52))), inference(resolution, [status(thm)], [c_12, c_102])).
% 3.25/1.51  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.25/1.51  tff(c_123, plain, (![B_57, B_56]: (B_57=B_56 | ~r1_tarski(B_56, B_57) | ~v1_xboole_0(B_57))), inference(resolution, [status(thm)], [c_112, c_8])).
% 3.25/1.51  tff(c_136, plain, (![B_7, B_50]: (B_7=B_50 | ~v1_xboole_0(B_50) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_111, c_123])).
% 3.25/1.51  tff(c_816, plain, (![B_164]: (B_164='#skF_3' | ~v1_xboole_0(B_164))), inference(resolution, [status(thm)], [c_804, c_136])).
% 3.25/1.51  tff(c_826, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_812, c_816])).
% 3.25/1.51  tff(c_803, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_164])).
% 3.25/1.51  tff(c_829, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_803, c_816])).
% 3.25/1.51  tff(c_848, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_826, c_829])).
% 3.25/1.51  tff(c_839, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_826, c_32])).
% 3.25/1.51  tff(c_872, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_848, c_839])).
% 3.25/1.51  tff(c_838, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_826, c_44])).
% 3.25/1.51  tff(c_22, plain, (![A_17, B_18, D_20]: (r2_relset_1(A_17, B_18, D_20, D_20) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.25/1.51  tff(c_899, plain, (r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_838, c_22])).
% 3.25/1.51  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_872, c_899])).
% 3.25/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  Inference rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Ref     : 0
% 3.25/1.51  #Sup     : 191
% 3.25/1.51  #Fact    : 0
% 3.25/1.51  #Define  : 0
% 3.25/1.51  #Split   : 8
% 3.25/1.51  #Chain   : 0
% 3.25/1.51  #Close   : 0
% 3.25/1.51  
% 3.25/1.51  Ordering : KBO
% 3.25/1.51  
% 3.25/1.51  Simplification rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Subsume      : 99
% 3.25/1.51  #Demod        : 98
% 3.25/1.51  #Tautology    : 44
% 3.25/1.51  #SimpNegUnit  : 16
% 3.25/1.51  #BackRed      : 31
% 3.25/1.51  
% 3.25/1.51  #Partial instantiations: 0
% 3.25/1.51  #Strategies tried      : 1
% 3.25/1.51  
% 3.25/1.51  Timing (in seconds)
% 3.25/1.51  ----------------------
% 3.25/1.52  Preprocessing        : 0.32
% 3.25/1.52  Parsing              : 0.17
% 3.25/1.52  CNF conversion       : 0.02
% 3.25/1.52  Main loop            : 0.42
% 3.25/1.52  Inferencing          : 0.15
% 3.25/1.52  Reduction            : 0.12
% 3.25/1.52  Demodulation         : 0.08
% 3.25/1.52  BG Simplification    : 0.02
% 3.25/1.52  Subsumption          : 0.09
% 3.25/1.52  Abstraction          : 0.02
% 3.25/1.52  MUC search           : 0.00
% 3.25/1.52  Cooper               : 0.00
% 3.25/1.52  Total                : 0.77
% 3.25/1.52  Index Insertion      : 0.00
% 3.25/1.52  Index Deletion       : 0.00
% 3.25/1.52  Index Matching       : 0.00
% 3.25/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
