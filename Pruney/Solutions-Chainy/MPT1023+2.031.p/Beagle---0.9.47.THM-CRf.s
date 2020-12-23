%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:21 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 102 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 386 expanded)
%              Number of equality atoms :    6 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_49,plain,(
    ! [B_26,A_27] :
      ( m1_subset_1(B_26,A_27)
      | ~ v1_xboole_0(B_26)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [E_19] :
      ( k1_funct_1('#skF_5',E_19) = k1_funct_1('#skF_6',E_19)
      | ~ m1_subset_1(E_19,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_58,plain,(
    ! [B_26] :
      ( k1_funct_1('#skF_5',B_26) = k1_funct_1('#skF_6',B_26)
      | ~ v1_xboole_0(B_26)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_49,c_20])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_93,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( r2_hidden('#skF_2'(A_33,B_34,C_35,D_36),A_33)
      | r2_relset_1(A_33,B_34,C_35,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(D_36,A_33,B_34)
      | ~ v1_funct_1(D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,(
    ! [C_35] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_35,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_35,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_35,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_139,plain,(
    ! [C_38] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_38,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_38,'#skF_6')
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_38,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_103])).

tff(c_150,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_160,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_150])).

tff(c_161,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_160])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_167,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_6])).

tff(c_173,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_167])).

tff(c_182,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_173,c_20])).

tff(c_14,plain,(
    ! [D_13,A_7,B_8,C_9] :
      ( k1_funct_1(D_13,'#skF_2'(A_7,B_8,C_9,D_13)) != k1_funct_1(C_9,'#skF_2'(A_7,B_8,C_9,D_13))
      | r2_relset_1(A_7,B_8,C_9,D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(D_13,A_7,B_8)
      | ~ v1_funct_1(D_13)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_190,plain,
    ( r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_14])).

tff(c_195,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_190])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_195])).

tff(c_199,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_210,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( r2_hidden('#skF_2'(A_44,B_45,C_46,D_47),A_44)
      | r2_relset_1(A_44,B_45,C_46,D_47)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_47,A_44,B_45)
      | ~ v1_funct_1(D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(C_46,A_44,B_45)
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_220,plain,(
    ! [C_46] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_46,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_46,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_46,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_46) ) ),
    inference(resolution,[status(thm)],[c_22,c_210])).

tff(c_260,plain,(
    ! [C_53] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_53,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_53,'#skF_6')
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_53,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_220])).

tff(c_271,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_260])).

tff(c_281,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_271])).

tff(c_282,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_281])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_291,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_282,c_2])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.43  
% 2.18/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.43  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 2.18/1.43  
% 2.18/1.43  %Foreground sorts:
% 2.18/1.43  
% 2.18/1.43  
% 2.18/1.43  %Background operators:
% 2.18/1.43  
% 2.18/1.43  
% 2.18/1.43  %Foreground operators:
% 2.18/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.18/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.18/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.18/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.43  
% 2.18/1.45  tff(f_85, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 2.18/1.45  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.18/1.45  tff(f_64, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 2.18/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.18/1.45  tff(c_18, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_30, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_26, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_24, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_22, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_49, plain, (![B_26, A_27]: (m1_subset_1(B_26, A_27) | ~v1_xboole_0(B_26) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.45  tff(c_20, plain, (![E_19]: (k1_funct_1('#skF_5', E_19)=k1_funct_1('#skF_6', E_19) | ~m1_subset_1(E_19, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.18/1.45  tff(c_58, plain, (![B_26]: (k1_funct_1('#skF_5', B_26)=k1_funct_1('#skF_6', B_26) | ~v1_xboole_0(B_26) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_49, c_20])).
% 2.18/1.45  tff(c_84, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 2.18/1.45  tff(c_93, plain, (![A_33, B_34, C_35, D_36]: (r2_hidden('#skF_2'(A_33, B_34, C_35, D_36), A_33) | r2_relset_1(A_33, B_34, C_35, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(D_36, A_33, B_34) | ~v1_funct_1(D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.45  tff(c_103, plain, (![C_35]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_35, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_35, '#skF_6') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_35, '#skF_3', '#skF_4') | ~v1_funct_1(C_35))), inference(resolution, [status(thm)], [c_22, c_93])).
% 2.18/1.45  tff(c_139, plain, (![C_38]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_38, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_38, '#skF_6') | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_38, '#skF_3', '#skF_4') | ~v1_funct_1(C_38))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_103])).
% 2.18/1.45  tff(c_150, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_139])).
% 2.18/1.45  tff(c_160, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_150])).
% 2.18/1.45  tff(c_161, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_18, c_160])).
% 2.18/1.45  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.45  tff(c_167, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_161, c_6])).
% 2.18/1.45  tff(c_173, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_84, c_167])).
% 2.18/1.45  tff(c_182, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_173, c_20])).
% 2.18/1.45  tff(c_14, plain, (![D_13, A_7, B_8, C_9]: (k1_funct_1(D_13, '#skF_2'(A_7, B_8, C_9, D_13))!=k1_funct_1(C_9, '#skF_2'(A_7, B_8, C_9, D_13)) | r2_relset_1(A_7, B_8, C_9, D_13) | ~m1_subset_1(D_13, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(D_13, A_7, B_8) | ~v1_funct_1(D_13) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.45  tff(c_190, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_182, c_14])).
% 2.18/1.45  tff(c_195, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_22, c_190])).
% 2.18/1.45  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_195])).
% 2.18/1.45  tff(c_199, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 2.18/1.45  tff(c_210, plain, (![A_44, B_45, C_46, D_47]: (r2_hidden('#skF_2'(A_44, B_45, C_46, D_47), A_44) | r2_relset_1(A_44, B_45, C_46, D_47) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_47, A_44, B_45) | ~v1_funct_1(D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(C_46, A_44, B_45) | ~v1_funct_1(C_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.45  tff(c_220, plain, (![C_46]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_46, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_46, '#skF_6') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_46, '#skF_3', '#skF_4') | ~v1_funct_1(C_46))), inference(resolution, [status(thm)], [c_22, c_210])).
% 2.18/1.45  tff(c_260, plain, (![C_53]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_53, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_53, '#skF_6') | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_53, '#skF_3', '#skF_4') | ~v1_funct_1(C_53))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_220])).
% 2.18/1.45  tff(c_271, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_260])).
% 2.18/1.45  tff(c_281, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_271])).
% 2.18/1.45  tff(c_282, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_18, c_281])).
% 2.18/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.45  tff(c_291, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_282, c_2])).
% 2.18/1.45  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_291])).
% 2.18/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.45  
% 2.18/1.45  Inference rules
% 2.18/1.45  ----------------------
% 2.18/1.45  #Ref     : 2
% 2.18/1.45  #Sup     : 48
% 2.18/1.45  #Fact    : 0
% 2.18/1.45  #Define  : 0
% 2.18/1.45  #Split   : 8
% 2.18/1.45  #Chain   : 0
% 2.18/1.45  #Close   : 0
% 2.18/1.45  
% 2.18/1.45  Ordering : KBO
% 2.18/1.45  
% 2.18/1.45  Simplification rules
% 2.18/1.45  ----------------------
% 2.18/1.45  #Subsume      : 8
% 2.18/1.45  #Demod        : 33
% 2.18/1.45  #Tautology    : 12
% 2.18/1.45  #SimpNegUnit  : 9
% 2.18/1.45  #BackRed      : 0
% 2.18/1.45  
% 2.18/1.45  #Partial instantiations: 0
% 2.18/1.45  #Strategies tried      : 1
% 2.18/1.45  
% 2.18/1.45  Timing (in seconds)
% 2.18/1.45  ----------------------
% 2.18/1.45  Preprocessing        : 0.36
% 2.18/1.45  Parsing              : 0.21
% 2.18/1.45  CNF conversion       : 0.02
% 2.18/1.45  Main loop            : 0.25
% 2.18/1.45  Inferencing          : 0.09
% 2.18/1.45  Reduction            : 0.08
% 2.18/1.45  Demodulation         : 0.05
% 2.18/1.45  BG Simplification    : 0.02
% 2.18/1.45  Subsumption          : 0.04
% 2.18/1.45  Abstraction          : 0.01
% 2.18/1.45  MUC search           : 0.00
% 2.18/1.45  Cooper               : 0.00
% 2.18/1.45  Total                : 0.65
% 2.18/1.45  Index Insertion      : 0.00
% 2.18/1.45  Index Deletion       : 0.00
% 2.18/1.45  Index Matching       : 0.00
% 2.18/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
