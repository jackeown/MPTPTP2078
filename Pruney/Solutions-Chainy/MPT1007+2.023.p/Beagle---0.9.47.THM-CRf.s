%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:14 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   78 (  95 expanded)
%              Number of leaves         :   41 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 171 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_239,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_247,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_239])).

tff(c_132,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_132])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_72,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_288,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_296,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_288])).

tff(c_634,plain,(
    ! [B_238,A_239,C_240] :
      ( k1_xboole_0 = B_238
      | k1_relset_1(A_239,B_238,C_240) = A_239
      | ~ v1_funct_2(C_240,A_239,B_238)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_637,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_634])).

tff(c_644,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_296,c_637])).

tff(c_645,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_644])).

tff(c_79,plain,(
    ! [A_57] : k2_tarski(A_57,A_57) = k1_tarski(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,(
    ! [A_57] : r2_hidden(A_57,k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_12])).

tff(c_676,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_85])).

tff(c_38,plain,(
    ! [C_21,B_20,A_19] :
      ( m1_subset_1(k1_funct_1(C_21,B_20),A_19)
      | ~ r2_hidden(B_20,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v5_relat_1(C_21,A_19)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_684,plain,(
    ! [A_19] :
      ( m1_subset_1(k1_funct_1('#skF_6','#skF_4'),A_19)
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_19)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_676,c_38])).

tff(c_2509,plain,(
    ! [A_5588] :
      ( m1_subset_1(k1_funct_1('#skF_6','#skF_4'),A_5588)
      | ~ v5_relat_1('#skF_6',A_5588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_74,c_684])).

tff(c_126,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(A_68,B_69)
      | v1_xboole_0(B_69)
      | ~ m1_subset_1(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_130,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_66])).

tff(c_131,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_2563,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_2509,c_131])).

tff(c_2584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_2563])).

tff(c_2585,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_3'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2686,plain,(
    ! [C_5663,B_5664,A_5665] :
      ( ~ v1_xboole_0(C_5663)
      | ~ m1_subset_1(B_5664,k1_zfmisc_1(C_5663))
      | ~ r2_hidden(A_5665,B_5664) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2694,plain,(
    ! [B_5666,A_5667,A_5668] :
      ( ~ v1_xboole_0(B_5666)
      | ~ r2_hidden(A_5667,A_5668)
      | ~ r1_tarski(A_5668,B_5666) ) ),
    inference(resolution,[status(thm)],[c_34,c_2686])).

tff(c_2717,plain,(
    ! [B_5672,A_5673] :
      ( ~ v1_xboole_0(B_5672)
      | ~ r1_tarski(A_5673,B_5672)
      | k1_xboole_0 = A_5673 ) ),
    inference(resolution,[status(thm)],[c_48,c_2694])).

tff(c_2736,plain,(
    ! [B_5677] :
      ( ~ v1_xboole_0(B_5677)
      | k1_xboole_0 = B_5677 ) ),
    inference(resolution,[status(thm)],[c_6,c_2717])).

tff(c_2739,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2585,c_2736])).

tff(c_2743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.81  
% 4.37/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 4.37/1.81  
% 4.37/1.81  %Foreground sorts:
% 4.37/1.81  
% 4.37/1.81  
% 4.37/1.81  %Background operators:
% 4.37/1.81  
% 4.37/1.81  
% 4.37/1.81  %Foreground operators:
% 4.37/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.37/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.37/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.37/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.37/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.37/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.37/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.37/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.37/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.37/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.37/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.81  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.37/1.81  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.37/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.37/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.37/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.81  
% 4.37/1.83  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 4.37/1.83  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.37/1.83  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.37/1.83  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.37/1.83  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.37/1.83  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.37/1.83  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.37/1.83  tff(f_71, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 4.37/1.83  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.37/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.37/1.83  tff(f_101, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 4.37/1.83  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.37/1.83  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.37/1.83  tff(c_68, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.37/1.83  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.37/1.83  tff(c_239, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/1.83  tff(c_247, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_239])).
% 4.37/1.83  tff(c_132, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.37/1.83  tff(c_140, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_132])).
% 4.37/1.83  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.37/1.83  tff(c_72, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.37/1.83  tff(c_288, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.37/1.83  tff(c_296, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_288])).
% 4.37/1.83  tff(c_634, plain, (![B_238, A_239, C_240]: (k1_xboole_0=B_238 | k1_relset_1(A_239, B_238, C_240)=A_239 | ~v1_funct_2(C_240, A_239, B_238) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.37/1.83  tff(c_637, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_70, c_634])).
% 4.37/1.83  tff(c_644, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_296, c_637])).
% 4.37/1.83  tff(c_645, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_644])).
% 4.37/1.83  tff(c_79, plain, (![A_57]: (k2_tarski(A_57, A_57)=k1_tarski(A_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.37/1.83  tff(c_12, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.83  tff(c_85, plain, (![A_57]: (r2_hidden(A_57, k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_12])).
% 4.37/1.83  tff(c_676, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_645, c_85])).
% 4.37/1.83  tff(c_38, plain, (![C_21, B_20, A_19]: (m1_subset_1(k1_funct_1(C_21, B_20), A_19) | ~r2_hidden(B_20, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v5_relat_1(C_21, A_19) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.37/1.83  tff(c_684, plain, (![A_19]: (m1_subset_1(k1_funct_1('#skF_6', '#skF_4'), A_19) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_19) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_676, c_38])).
% 4.37/1.83  tff(c_2509, plain, (![A_5588]: (m1_subset_1(k1_funct_1('#skF_6', '#skF_4'), A_5588) | ~v5_relat_1('#skF_6', A_5588))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_74, c_684])).
% 4.37/1.83  tff(c_126, plain, (![A_68, B_69]: (r2_hidden(A_68, B_69) | v1_xboole_0(B_69) | ~m1_subset_1(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.37/1.83  tff(c_66, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.37/1.83  tff(c_130, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_126, c_66])).
% 4.37/1.83  tff(c_131, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_130])).
% 4.37/1.83  tff(c_2563, plain, (~v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_2509, c_131])).
% 4.37/1.83  tff(c_2584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_2563])).
% 4.37/1.83  tff(c_2585, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_130])).
% 4.37/1.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.83  tff(c_48, plain, (![A_31]: (r2_hidden('#skF_3'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.37/1.83  tff(c_34, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.37/1.83  tff(c_2686, plain, (![C_5663, B_5664, A_5665]: (~v1_xboole_0(C_5663) | ~m1_subset_1(B_5664, k1_zfmisc_1(C_5663)) | ~r2_hidden(A_5665, B_5664))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.37/1.83  tff(c_2694, plain, (![B_5666, A_5667, A_5668]: (~v1_xboole_0(B_5666) | ~r2_hidden(A_5667, A_5668) | ~r1_tarski(A_5668, B_5666))), inference(resolution, [status(thm)], [c_34, c_2686])).
% 4.37/1.83  tff(c_2717, plain, (![B_5672, A_5673]: (~v1_xboole_0(B_5672) | ~r1_tarski(A_5673, B_5672) | k1_xboole_0=A_5673)), inference(resolution, [status(thm)], [c_48, c_2694])).
% 4.37/1.83  tff(c_2736, plain, (![B_5677]: (~v1_xboole_0(B_5677) | k1_xboole_0=B_5677)), inference(resolution, [status(thm)], [c_6, c_2717])).
% 4.37/1.83  tff(c_2739, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2585, c_2736])).
% 4.37/1.83  tff(c_2743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2739])).
% 4.37/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.83  
% 4.37/1.83  Inference rules
% 4.37/1.83  ----------------------
% 4.37/1.83  #Ref     : 2
% 4.37/1.83  #Sup     : 371
% 4.37/1.83  #Fact    : 6
% 4.37/1.83  #Define  : 0
% 4.37/1.83  #Split   : 6
% 4.37/1.83  #Chain   : 0
% 4.37/1.83  #Close   : 0
% 4.37/1.83  
% 4.37/1.83  Ordering : KBO
% 4.37/1.83  
% 4.37/1.83  Simplification rules
% 4.37/1.83  ----------------------
% 4.37/1.83  #Subsume      : 57
% 4.37/1.83  #Demod        : 103
% 4.37/1.83  #Tautology    : 97
% 4.37/1.83  #SimpNegUnit  : 16
% 4.37/1.83  #BackRed      : 20
% 4.37/1.83  
% 4.37/1.83  #Partial instantiations: 3280
% 4.37/1.83  #Strategies tried      : 1
% 4.37/1.83  
% 4.37/1.83  Timing (in seconds)
% 4.37/1.83  ----------------------
% 4.37/1.83  Preprocessing        : 0.36
% 4.37/1.83  Parsing              : 0.19
% 4.37/1.83  CNF conversion       : 0.03
% 4.37/1.83  Main loop            : 0.67
% 4.37/1.83  Inferencing          : 0.33
% 4.37/1.83  Reduction            : 0.16
% 4.37/1.83  Demodulation         : 0.11
% 4.37/1.83  BG Simplification    : 0.03
% 4.37/1.83  Subsumption          : 0.10
% 4.37/1.83  Abstraction          : 0.03
% 4.37/1.83  MUC search           : 0.00
% 4.37/1.83  Cooper               : 0.00
% 4.37/1.83  Total                : 1.06
% 4.37/1.83  Index Insertion      : 0.00
% 4.37/1.83  Index Deletion       : 0.00
% 4.37/1.83  Index Matching       : 0.00
% 4.37/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
