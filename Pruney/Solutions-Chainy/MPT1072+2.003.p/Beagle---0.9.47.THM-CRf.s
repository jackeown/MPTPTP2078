%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:56 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 117 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 313 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    ! [D_29,C_28,A_26,B_27] :
      ( r2_hidden(k1_funct_1(D_29,C_28),k2_relset_1(A_26,B_27,D_29))
      | k1_xboole_0 = B_27
      | ~ r2_hidden(C_28,A_26)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(D_29,A_26,B_27)
      | ~ v1_funct_1(D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_258,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k3_funct_2(A_93,B_94,C_95,D_96) = k1_funct_1(C_95,D_96)
      | ~ m1_subset_1(D_96,A_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_2(C_95,A_93,B_94)
      | ~ v1_funct_1(C_95)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_270,plain,(
    ! [B_94,C_95] :
      ( k3_funct_2('#skF_1',B_94,C_95,'#skF_3') = k1_funct_1(C_95,'#skF_3')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_94)))
      | ~ v1_funct_2(C_95,'#skF_1',B_94)
      | ~ v1_funct_1(C_95)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_258])).

tff(c_283,plain,(
    ! [B_97,C_98] :
      ( k3_funct_2('#skF_1',B_97,C_98,'#skF_3') = k1_funct_1(C_98,'#skF_3')
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_97)))
      | ~ v1_funct_2(C_98,'#skF_1',B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_270])).

tff(c_290,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_283])).

tff(c_302,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_290])).

tff(c_36,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_312,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_36])).

tff(c_319,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_312])).

tff(c_325,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_319])).

tff(c_327,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_347,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_327])).

tff(c_350,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_347])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_350])).

tff(c_353,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [B_53,A_54] :
      ( v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,(
    ! [A_6] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_113,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_xboole_0(B_3,A_2)
      | ~ r1_tarski(B_3,A_2)
      | v1_xboole_0(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [B_58,A_59] :
      ( ~ r1_xboole_0(B_58,A_59)
      | ~ r1_tarski(B_58,A_59) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_4])).

tff(c_130,plain,(
    ! [A_60] : ~ r1_tarski(A_60,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_135,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_87,c_130])).

tff(c_136,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_360,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_136])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.32  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.41/1.32  
% 2.41/1.32  %Foreground sorts:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Background operators:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Foreground operators:
% 2.41/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.41/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.41/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.32  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.41/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.32  
% 2.41/1.33  tff(f_135, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.41/1.33  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.41/1.33  tff(f_115, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.41/1.33  tff(f_103, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.41/1.33  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.41/1.33  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.41/1.33  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.41/1.33  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.41/1.33  tff(f_35, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.41/1.33  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.41/1.33  tff(c_48, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.41/1.33  tff(c_44, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.41/1.33  tff(c_16, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.41/1.33  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.41/1.33  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.41/1.33  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.41/1.33  tff(c_34, plain, (![D_29, C_28, A_26, B_27]: (r2_hidden(k1_funct_1(D_29, C_28), k2_relset_1(A_26, B_27, D_29)) | k1_xboole_0=B_27 | ~r2_hidden(C_28, A_26) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(D_29, A_26, B_27) | ~v1_funct_1(D_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.41/1.33  tff(c_258, plain, (![A_93, B_94, C_95, D_96]: (k3_funct_2(A_93, B_94, C_95, D_96)=k1_funct_1(C_95, D_96) | ~m1_subset_1(D_96, A_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_2(C_95, A_93, B_94) | ~v1_funct_1(C_95) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.41/1.33  tff(c_270, plain, (![B_94, C_95]: (k3_funct_2('#skF_1', B_94, C_95, '#skF_3')=k1_funct_1(C_95, '#skF_3') | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_94))) | ~v1_funct_2(C_95, '#skF_1', B_94) | ~v1_funct_1(C_95) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_258])).
% 2.41/1.33  tff(c_283, plain, (![B_97, C_98]: (k3_funct_2('#skF_1', B_97, C_98, '#skF_3')=k1_funct_1(C_98, '#skF_3') | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_97))) | ~v1_funct_2(C_98, '#skF_1', B_97) | ~v1_funct_1(C_98))), inference(negUnitSimplification, [status(thm)], [c_48, c_270])).
% 2.41/1.33  tff(c_290, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_283])).
% 2.41/1.33  tff(c_302, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_290])).
% 2.41/1.33  tff(c_36, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.41/1.33  tff(c_312, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_36])).
% 2.41/1.33  tff(c_319, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_312])).
% 2.41/1.33  tff(c_325, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_319])).
% 2.41/1.33  tff(c_327, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_325])).
% 2.41/1.33  tff(c_347, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_327])).
% 2.41/1.33  tff(c_350, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_347])).
% 2.41/1.33  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_350])).
% 2.41/1.33  tff(c_353, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_325])).
% 2.41/1.33  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.33  tff(c_75, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.33  tff(c_87, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_12, c_75])).
% 2.41/1.33  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.33  tff(c_100, plain, (![B_53, A_54]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.33  tff(c_112, plain, (![A_6]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_12, c_100])).
% 2.41/1.33  tff(c_113, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitLeft, [status(thm)], [c_112])).
% 2.41/1.33  tff(c_4, plain, (![B_3, A_2]: (~r1_xboole_0(B_3, A_2) | ~r1_tarski(B_3, A_2) | v1_xboole_0(B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.33  tff(c_125, plain, (![B_58, A_59]: (~r1_xboole_0(B_58, A_59) | ~r1_tarski(B_58, A_59))), inference(negUnitSimplification, [status(thm)], [c_113, c_4])).
% 2.41/1.33  tff(c_130, plain, (![A_60]: (~r1_tarski(A_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_125])).
% 2.41/1.33  tff(c_135, plain, $false, inference(resolution, [status(thm)], [c_87, c_130])).
% 2.41/1.33  tff(c_136, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_112])).
% 2.41/1.33  tff(c_360, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_136])).
% 2.41/1.33  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_360])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 59
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 5
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 9
% 2.41/1.33  #Demod        : 42
% 2.41/1.33  #Tautology    : 21
% 2.41/1.33  #SimpNegUnit  : 13
% 2.41/1.33  #BackRed      : 14
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 0
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.34  Preprocessing        : 0.32
% 2.41/1.34  Parsing              : 0.17
% 2.41/1.34  CNF conversion       : 0.02
% 2.41/1.34  Main loop            : 0.24
% 2.41/1.34  Inferencing          : 0.08
% 2.41/1.34  Reduction            : 0.07
% 2.41/1.34  Demodulation         : 0.05
% 2.41/1.34  BG Simplification    : 0.02
% 2.41/1.34  Subsumption          : 0.05
% 2.41/1.34  Abstraction          : 0.01
% 2.41/1.34  MUC search           : 0.00
% 2.41/1.34  Cooper               : 0.00
% 2.41/1.34  Total                : 0.60
% 2.41/1.34  Index Insertion      : 0.00
% 2.41/1.34  Index Deletion       : 0.00
% 2.41/1.34  Index Matching       : 0.00
% 2.41/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
