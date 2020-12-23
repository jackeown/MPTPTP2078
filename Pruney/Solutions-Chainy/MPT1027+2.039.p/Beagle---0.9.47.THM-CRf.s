%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:47 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 469 expanded)
%              Number of leaves         :   29 ( 172 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 (1336 expanded)
%              Number of equality atoms :   43 ( 371 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_88,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_2)).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44])).

tff(c_46,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_239,plain,(
    ! [B_60,C_61,A_62] :
      ( k1_xboole_0 = B_60
      | v1_funct_2(C_61,A_62,B_60)
      | k1_relset_1(A_62,B_60,C_61) != A_62
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_245,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_239])).

tff(c_256,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_245])).

tff(c_257,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_256])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_281,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_2])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_280,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_257,c_6])).

tff(c_111,plain,(
    ! [C_33,B_34,A_35] :
      ( ~ v1_xboole_0(C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_35,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_123,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_358,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_123])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_358])).

tff(c_450,plain,(
    ! [A_81] : ~ r2_hidden(A_81,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_455,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_450])).

tff(c_24,plain,(
    ! [B_17,C_18,A_16] :
      ( k1_xboole_0 = B_17
      | v1_funct_2(C_18,A_16,B_17)
      | k1_relset_1(A_16,B_17,C_18) != A_16
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_643,plain,(
    ! [B_107,C_108,A_109] :
      ( B_107 = '#skF_5'
      | v1_funct_2(C_108,A_109,B_107)
      | k1_relset_1(A_109,B_107,C_108) != A_109
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_24])).

tff(c_655,plain,
    ( '#skF_5' = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_643])).

tff(c_661,plain,
    ( '#skF_5' = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_655])).

tff(c_662,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_661])).

tff(c_515,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_1'(A_89),A_89)
      | A_89 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_12])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_30] : m1_subset_1('#skF_2'(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_94,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_113,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_35,'#skF_2'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_94,c_111])).

tff(c_120,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_2'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_485,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_120])).

tff(c_527,plain,(
    '#skF_2'('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_515,c_485])).

tff(c_32,plain,(
    ! [A_19] : v1_funct_2('#skF_2'(A_19),A_19,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_544,plain,(
    v1_funct_2('#skF_5','#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_32])).

tff(c_670,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_662,c_662,c_544])).

tff(c_366,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_371,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_366])).

tff(c_18,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_16,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).

tff(c_365,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_382,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_365])).

tff(c_424,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_1'(A_77),A_77)
      | A_77 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_12])).

tff(c_413,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_120])).

tff(c_436,plain,(
    '#skF_2'('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_424,c_413])).

tff(c_372,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_94])).

tff(c_444,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_372])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_444])).

tff(c_448,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16 ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_472,plain,(
    ! [A_16] :
      ( v1_funct_2('#skF_5',A_16,'#skF_5')
      | A_16 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_455,c_455,c_448])).

tff(c_803,plain,(
    ! [A_117] :
      ( v1_funct_2('#skF_4',A_117,'#skF_4')
      | A_117 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_662,c_662,c_472])).

tff(c_688,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_52])).

tff(c_810,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_803,c_688])).

tff(c_815,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_688])).

tff(c_819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.45  
% 2.93/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.45  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.93/1.45  
% 2.93/1.45  %Foreground sorts:
% 2.93/1.45  
% 2.93/1.45  
% 2.93/1.45  %Background operators:
% 2.93/1.45  
% 2.93/1.45  
% 2.93/1.45  %Foreground operators:
% 2.93/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.93/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.93/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.93/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.93/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.93/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.93/1.45  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.93/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.45  
% 2.93/1.46  tff(f_101, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.93/1.46  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.93/1.46  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.93/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.93/1.46  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.93/1.46  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.93/1.46  tff(f_88, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_funct_2)).
% 2.93/1.46  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_44, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_52, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44])).
% 2.93/1.46  tff(c_46, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.46  tff(c_239, plain, (![B_60, C_61, A_62]: (k1_xboole_0=B_60 | v1_funct_2(C_61, A_62, B_60) | k1_relset_1(A_62, B_60, C_61)!=A_62 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_60))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_245, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_239])).
% 2.93/1.46  tff(c_256, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_245])).
% 2.93/1.46  tff(c_257, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_256])).
% 2.93/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.93/1.46  tff(c_281, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_2])).
% 2.93/1.46  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.46  tff(c_280, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_257, c_6])).
% 2.93/1.46  tff(c_111, plain, (![C_33, B_34, A_35]: (~v1_xboole_0(C_33) | ~m1_subset_1(B_34, k1_zfmisc_1(C_33)) | ~r2_hidden(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.46  tff(c_122, plain, (![A_35]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_35, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_111])).
% 2.93/1.46  tff(c_123, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_122])).
% 2.93/1.46  tff(c_358, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_123])).
% 2.93/1.46  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_358])).
% 2.93/1.46  tff(c_450, plain, (![A_81]: (~r2_hidden(A_81, '#skF_5'))), inference(splitRight, [status(thm)], [c_122])).
% 2.93/1.46  tff(c_455, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12, c_450])).
% 2.93/1.46  tff(c_24, plain, (![B_17, C_18, A_16]: (k1_xboole_0=B_17 | v1_funct_2(C_18, A_16, B_17) | k1_relset_1(A_16, B_17, C_18)!=A_16 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_643, plain, (![B_107, C_108, A_109]: (B_107='#skF_5' | v1_funct_2(C_108, A_109, B_107) | k1_relset_1(A_109, B_107, C_108)!=A_109 | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_24])).
% 2.93/1.46  tff(c_655, plain, ('#skF_5'='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_643])).
% 2.93/1.46  tff(c_661, plain, ('#skF_5'='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_655])).
% 2.93/1.46  tff(c_662, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_661])).
% 2.93/1.46  tff(c_515, plain, (![A_89]: (r2_hidden('#skF_1'(A_89), A_89) | A_89='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_455, c_12])).
% 2.93/1.46  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.46  tff(c_90, plain, (![A_30]: (m1_subset_1('#skF_2'(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.46  tff(c_94, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 2.93/1.46  tff(c_113, plain, (![A_35]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_35, '#skF_2'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_94, c_111])).
% 2.93/1.46  tff(c_120, plain, (![A_35]: (~r2_hidden(A_35, '#skF_2'(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_113])).
% 2.93/1.46  tff(c_485, plain, (![A_35]: (~r2_hidden(A_35, '#skF_2'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_120])).
% 2.93/1.46  tff(c_527, plain, ('#skF_2'('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_515, c_485])).
% 2.93/1.46  tff(c_32, plain, (![A_19]: (v1_funct_2('#skF_2'(A_19), A_19, A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.46  tff(c_544, plain, (v1_funct_2('#skF_5', '#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_527, c_32])).
% 2.93/1.46  tff(c_670, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_662, c_662, c_544])).
% 2.93/1.46  tff(c_366, plain, (![A_70]: (~r2_hidden(A_70, '#skF_5'))), inference(splitRight, [status(thm)], [c_122])).
% 2.93/1.46  tff(c_371, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12, c_366])).
% 2.93/1.46  tff(c_18, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_16, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_56, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18])).
% 2.93/1.46  tff(c_365, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_56])).
% 2.93/1.46  tff(c_382, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_365])).
% 2.93/1.46  tff(c_424, plain, (![A_77]: (r2_hidden('#skF_1'(A_77), A_77) | A_77='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_12])).
% 2.93/1.46  tff(c_413, plain, (![A_35]: (~r2_hidden(A_35, '#skF_2'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_120])).
% 2.93/1.46  tff(c_436, plain, ('#skF_2'('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_424, c_413])).
% 2.93/1.46  tff(c_372, plain, (m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_94])).
% 2.93/1.46  tff(c_444, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_372])).
% 2.93/1.46  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_444])).
% 2.93/1.46  tff(c_448, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16)), inference(splitRight, [status(thm)], [c_56])).
% 2.93/1.46  tff(c_472, plain, (![A_16]: (v1_funct_2('#skF_5', A_16, '#skF_5') | A_16='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_455, c_455, c_455, c_448])).
% 2.93/1.46  tff(c_803, plain, (![A_117]: (v1_funct_2('#skF_4', A_117, '#skF_4') | A_117='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_662, c_662, c_472])).
% 2.93/1.46  tff(c_688, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_52])).
% 2.93/1.46  tff(c_810, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_803, c_688])).
% 2.93/1.46  tff(c_815, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_810, c_688])).
% 2.93/1.46  tff(c_819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_670, c_815])).
% 2.93/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  Inference rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Ref     : 0
% 2.93/1.46  #Sup     : 155
% 2.93/1.46  #Fact    : 0
% 2.93/1.46  #Define  : 0
% 2.93/1.46  #Split   : 3
% 2.93/1.46  #Chain   : 0
% 2.93/1.46  #Close   : 0
% 2.93/1.46  
% 2.93/1.46  Ordering : KBO
% 2.93/1.46  
% 2.93/1.46  Simplification rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Subsume      : 18
% 2.93/1.46  #Demod        : 239
% 2.93/1.46  #Tautology    : 99
% 3.07/1.46  #SimpNegUnit  : 4
% 3.07/1.46  #BackRed      : 73
% 3.07/1.46  
% 3.07/1.46  #Partial instantiations: 0
% 3.07/1.46  #Strategies tried      : 1
% 3.07/1.46  
% 3.07/1.46  Timing (in seconds)
% 3.07/1.46  ----------------------
% 3.07/1.47  Preprocessing        : 0.31
% 3.07/1.47  Parsing              : 0.18
% 3.07/1.47  CNF conversion       : 0.02
% 3.07/1.47  Main loop            : 0.33
% 3.07/1.47  Inferencing          : 0.11
% 3.07/1.47  Reduction            : 0.11
% 3.07/1.47  Demodulation         : 0.08
% 3.07/1.47  BG Simplification    : 0.02
% 3.07/1.47  Subsumption          : 0.05
% 3.07/1.47  Abstraction          : 0.02
% 3.07/1.47  MUC search           : 0.00
% 3.07/1.47  Cooper               : 0.00
% 3.07/1.47  Total                : 0.68
% 3.07/1.47  Index Insertion      : 0.00
% 3.07/1.47  Index Deletion       : 0.00
% 3.07/1.47  Index Matching       : 0.00
% 3.07/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
