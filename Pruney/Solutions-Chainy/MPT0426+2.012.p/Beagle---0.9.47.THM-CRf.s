%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:56 EST 2020

% Result     : Theorem 13.29s
% Output     : CNFRefutation 13.29s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 395 expanded)
%              Number of leaves         :   37 ( 137 expanded)
%              Depth                    :   10
%              Number of atoms          :  251 ( 918 expanded)
%              Number of equality atoms :   74 ( 149 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > o_2_1_setfam_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(o_2_1_setfam_1,type,(
    o_2_1_setfam_1: ( $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_64,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_92,plain,(
    ! [B_45,A_46] :
      ( ~ r2_hidden(B_45,A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_38290,plain,(
    ! [A_52679,B_52680] :
      ( r2_hidden('#skF_5'(A_52679,B_52680),A_52679)
      | r1_tarski(B_52680,k1_setfam_1(A_52679))
      | k1_xboole_0 = A_52679 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_103,plain,(
    ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_78,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8'))
      | r2_hidden('#skF_7',D_41)
      | ~ r2_hidden(D_41,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_35101,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_7',D_41)
      | ~ r2_hidden(D_41,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_78])).

tff(c_38324,plain,(
    ! [B_52680] :
      ( r2_hidden('#skF_7','#skF_5'('#skF_8',B_52680))
      | r1_tarski(B_52680,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_38290,c_35101])).

tff(c_40284,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_38324])).

tff(c_46,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [A_25] :
      ( k8_setfam_1(A_25,k1_xboole_0) = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_80,plain,(
    ! [A_25] : k8_setfam_1(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_40306,plain,(
    ! [A_25] : k8_setfam_1(A_25,'#skF_8') = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40284,c_80])).

tff(c_35181,plain,(
    ! [B_49925,A_49926] :
      ( m1_subset_1(B_49925,A_49926)
      | ~ r2_hidden(B_49925,A_49926)
      | v1_xboole_0(A_49926) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_35199,plain,
    ( m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_35181])).

tff(c_35211,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_35199])).

tff(c_35737,plain,(
    ! [A_49971,B_49972] :
      ( r2_hidden('#skF_5'(A_49971,B_49972),A_49971)
      | r1_tarski(B_49972,k1_setfam_1(A_49971))
      | k1_xboole_0 = A_49971 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_35771,plain,(
    ! [B_49972] :
      ( r2_hidden('#skF_7','#skF_5'('#skF_8',B_49972))
      | r1_tarski(B_49972,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_35737,c_35101])).

tff(c_37649,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_35771])).

tff(c_37670,plain,(
    ! [A_25] : k8_setfam_1(A_25,'#skF_8') = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37649,c_80])).

tff(c_161,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_184,plain,
    ( ~ m1_subset_1('#skF_7',k8_setfam_1('#skF_6','#skF_8'))
    | v1_xboole_0(k8_setfam_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_161,c_103])).

tff(c_35650,plain,(
    ~ m1_subset_1('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_37781,plain,(
    ~ m1_subset_1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37670,c_35650])).

tff(c_37787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35211,c_37781])).

tff(c_37789,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_35771])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35102,plain,(
    ! [D_49918] :
      ( r2_hidden('#skF_7',D_49918)
      | ~ r2_hidden(D_49918,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_78])).

tff(c_35114,plain,
    ( r2_hidden('#skF_7','#skF_1'('#skF_8'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_35102])).

tff(c_35120,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_35114])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35877,plain,(
    ! [A_49981,B_49982] :
      ( ~ v1_xboole_0(A_49981)
      | r1_tarski(B_49982,k1_setfam_1(A_49981))
      | k1_xboole_0 = A_49981 ) ),
    inference(resolution,[status(thm)],[c_35737,c_2])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_35906,plain,(
    ! [A_17,A_49981] :
      ( r2_hidden(A_17,k1_setfam_1(A_49981))
      | ~ v1_xboole_0(A_49981)
      | k1_xboole_0 = A_49981 ) ),
    inference(resolution,[status(thm)],[c_35877,c_28])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_35430,plain,(
    ! [A_49944,B_49945] :
      ( k6_setfam_1(A_49944,B_49945) = k1_setfam_1(B_49945)
      | ~ m1_subset_1(B_49945,k1_zfmisc_1(k1_zfmisc_1(A_49944))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_35450,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_35430])).

tff(c_38132,plain,(
    ! [A_52574,B_52575] :
      ( k8_setfam_1(A_52574,B_52575) = k6_setfam_1(A_52574,B_52575)
      | k1_xboole_0 = B_52575
      | ~ m1_subset_1(B_52575,k1_zfmisc_1(k1_zfmisc_1(A_52574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38145,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_66,c_38132])).

tff(c_38155,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35450,c_38145])).

tff(c_38156,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_37789,c_38155])).

tff(c_38164,plain,(
    ~ r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38156,c_103])).

tff(c_38186,plain,
    ( ~ v1_xboole_0('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_35906,c_38164])).

tff(c_38198,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35120,c_38186])).

tff(c_38200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37789,c_38198])).

tff(c_38201,plain,(
    v1_xboole_0(k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_40379,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40306,c_38201])).

tff(c_40385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_40379])).

tff(c_40387,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_38324])).

tff(c_40388,plain,(
    ! [A_55176,B_55177] :
      ( k8_setfam_1(A_55176,B_55177) = k6_setfam_1(A_55176,B_55177)
      | k1_xboole_0 = B_55177
      | ~ m1_subset_1(B_55177,k1_zfmisc_1(k1_zfmisc_1(A_55176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40401,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_66,c_40388])).

tff(c_40411,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35450,c_40401])).

tff(c_40417,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_40387,c_40411])).

tff(c_40419,plain,(
    v1_xboole_0(k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40417,c_38201])).

tff(c_38430,plain,(
    ! [A_52689,B_52690] :
      ( ~ v1_xboole_0(A_52689)
      | r1_tarski(B_52690,k1_setfam_1(A_52689))
      | k1_xboole_0 = A_52689 ) ),
    inference(resolution,[status(thm)],[c_38290,c_2])).

tff(c_35277,plain,(
    ! [C_49934,B_49935,A_49936] :
      ( r2_hidden(C_49934,B_49935)
      | ~ r2_hidden(C_49934,A_49936)
      | ~ r1_tarski(A_49936,B_49935) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35330,plain,(
    ! [B_49940] :
      ( r2_hidden('#skF_7',B_49940)
      | ~ r1_tarski('#skF_6',B_49940) ) ),
    inference(resolution,[status(thm)],[c_64,c_35277])).

tff(c_35369,plain,(
    ! [B_49940] :
      ( ~ v1_xboole_0(B_49940)
      | ~ r1_tarski('#skF_6',B_49940) ) ),
    inference(resolution,[status(thm)],[c_35330,c_2])).

tff(c_38458,plain,(
    ! [A_52689] :
      ( ~ v1_xboole_0(k1_setfam_1(A_52689))
      | ~ v1_xboole_0(A_52689)
      | k1_xboole_0 = A_52689 ) ),
    inference(resolution,[status(thm)],[c_38430,c_35369])).

tff(c_40430,plain,
    ( ~ v1_xboole_0('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_40419,c_38458])).

tff(c_40433,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35120,c_40430])).

tff(c_40435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40387,c_40433])).

tff(c_40437,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_35114])).

tff(c_41022,plain,(
    ! [A_55303,B_55304] :
      ( r2_hidden('#skF_5'(A_55303,B_55304),A_55303)
      | r1_tarski(B_55304,k1_setfam_1(A_55303))
      | k1_xboole_0 = A_55303 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_41051,plain,(
    ! [B_55304] :
      ( r2_hidden('#skF_7','#skF_5'('#skF_8',B_55304))
      | r1_tarski(B_55304,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_41022,c_35101])).

tff(c_43215,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_41051])).

tff(c_14,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_99,plain,(
    ! [C_14] : ~ v1_xboole_0(k1_tarski(C_14)) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_40442,plain,(
    ! [A_55258,B_55259] :
      ( k4_xboole_0(k1_tarski(A_55258),B_55259) = k1_xboole_0
      | ~ r2_hidden(A_55258,B_55259) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40544,plain,(
    ! [C_55265,A_55266] :
      ( ~ r2_hidden(C_55265,k1_xboole_0)
      | ~ r2_hidden(A_55266,k1_tarski(C_55265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40442,c_34])).

tff(c_40556,plain,(
    ! [C_55265] :
      ( ~ r2_hidden(C_55265,k1_xboole_0)
      | v1_xboole_0(k1_tarski(C_55265)) ) ),
    inference(resolution,[status(thm)],[c_4,c_40544])).

tff(c_40568,plain,(
    ! [C_55267] : ~ r2_hidden(C_55267,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_40556])).

tff(c_40583,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_40568])).

tff(c_43232,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43215,c_40583])).

tff(c_43239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40437,c_43232])).

tff(c_43241,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_41051])).

tff(c_40941,plain,(
    ! [A_55297,B_55298] :
      ( k6_setfam_1(A_55297,B_55298) = k1_setfam_1(B_55298)
      | ~ m1_subset_1(B_55298,k1_zfmisc_1(k1_zfmisc_1(A_55297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40961,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_40941])).

tff(c_43488,plain,(
    ! [A_58117,B_58118] :
      ( k8_setfam_1(A_58117,B_58118) = k6_setfam_1(A_58117,B_58118)
      | k1_xboole_0 = B_58118
      | ~ m1_subset_1(B_58118,k1_zfmisc_1(k1_zfmisc_1(A_58117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_43501,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_66,c_43488])).

tff(c_43511,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40961,c_43501])).

tff(c_43512,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_43241,c_43511])).

tff(c_43521,plain,(
    ~ r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43512,c_103])).

tff(c_43240,plain,(
    ! [B_55304] :
      ( r2_hidden('#skF_7','#skF_5'('#skF_8',B_55304))
      | r1_tarski(B_55304,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_41051])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k1_tarski(A_17),B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42029,plain,(
    ! [B_57537,A_57538] :
      ( ~ r1_tarski(B_57537,'#skF_5'(A_57538,B_57537))
      | r1_tarski(B_57537,k1_setfam_1(A_57538))
      | k1_xboole_0 = A_57538 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_47445,plain,(
    ! [A_60759,A_60760] :
      ( r1_tarski(k1_tarski(A_60759),k1_setfam_1(A_60760))
      | k1_xboole_0 = A_60760
      | ~ r2_hidden(A_60759,'#skF_5'(A_60760,k1_tarski(A_60759))) ) ),
    inference(resolution,[status(thm)],[c_30,c_42029])).

tff(c_47457,plain,
    ( k1_xboole_0 = '#skF_8'
    | r1_tarski(k1_tarski('#skF_7'),k1_setfam_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_43240,c_47445])).

tff(c_47504,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_setfam_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_43241,c_47457])).

tff(c_47525,plain,(
    r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_47504,c_28])).

tff(c_47589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43521,c_47525])).

tff(c_47590,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_47700,plain,(
    ! [A_60824,B_60825] :
      ( r2_hidden('#skF_2'(A_60824,B_60825),A_60824)
      | r1_tarski(A_60824,B_60825) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47712,plain,(
    ! [A_60824] : r1_tarski(A_60824,A_60824) ),
    inference(resolution,[status(thm)],[c_47700,c_8])).

tff(c_47591,plain,(
    r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_70,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_47597,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47591,c_70])).

tff(c_47885,plain,(
    ! [C_60842,B_60843,A_60844] :
      ( r2_hidden(C_60842,B_60843)
      | ~ r2_hidden(C_60842,A_60844)
      | ~ r1_tarski(A_60844,B_60843) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47903,plain,(
    ! [B_60843] :
      ( r2_hidden('#skF_9',B_60843)
      | ~ r1_tarski('#skF_8',B_60843) ) ),
    inference(resolution,[status(thm)],[c_47597,c_47885])).

tff(c_56,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k1_setfam_1(B_32),A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48039,plain,(
    ! [A_60853,B_60854] :
      ( k6_setfam_1(A_60853,B_60854) = k1_setfam_1(B_60854)
      | ~ m1_subset_1(B_60854,k1_zfmisc_1(k1_zfmisc_1(A_60853))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48059,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_48039])).

tff(c_50395,plain,(
    ! [A_63320,B_63321] :
      ( k8_setfam_1(A_63320,B_63321) = k6_setfam_1(A_63320,B_63321)
      | k1_xboole_0 = B_63321
      | ~ m1_subset_1(B_63321,k1_zfmisc_1(k1_zfmisc_1(A_63320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50408,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_66,c_50395])).

tff(c_50418,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48059,c_50408])).

tff(c_50422,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_50418])).

tff(c_47907,plain,(
    ! [B_60845] :
      ( r2_hidden('#skF_9',B_60845)
      | ~ r1_tarski('#skF_8',B_60845) ) ),
    inference(resolution,[status(thm)],[c_47597,c_47885])).

tff(c_47722,plain,(
    ! [A_60827,B_60828] :
      ( k4_xboole_0(k1_tarski(A_60827),B_60828) = k1_xboole_0
      | ~ r2_hidden(A_60827,B_60828) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47745,plain,(
    ! [C_60831,A_60832] :
      ( ~ r2_hidden(C_60831,k1_xboole_0)
      | ~ r2_hidden(A_60832,k1_tarski(C_60831)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47722,c_34])).

tff(c_47757,plain,(
    ! [C_60831] :
      ( ~ r2_hidden(C_60831,k1_xboole_0)
      | v1_xboole_0(k1_tarski(C_60831)) ) ),
    inference(resolution,[status(thm)],[c_4,c_47745])).

tff(c_47767,plain,(
    ! [C_60831] : ~ r2_hidden(C_60831,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_47757])).

tff(c_47935,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_47907,c_47767])).

tff(c_50438,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50422,c_47935])).

tff(c_50448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47712,c_50438])).

tff(c_50449,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_50418])).

tff(c_47904,plain,(
    ! [B_60843] :
      ( r2_hidden('#skF_7',B_60843)
      | ~ r1_tarski(k8_setfam_1('#skF_6','#skF_8'),B_60843) ) ),
    inference(resolution,[status(thm)],[c_47591,c_47885])).

tff(c_50548,plain,(
    ! [B_63524] :
      ( r2_hidden('#skF_7',B_63524)
      | ~ r1_tarski(k1_setfam_1('#skF_8'),B_63524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50449,c_47904])).

tff(c_50570,plain,(
    ! [A_63545] :
      ( r2_hidden('#skF_7',A_63545)
      | ~ r2_hidden(A_63545,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_50548])).

tff(c_50585,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_47903,c_50570])).

tff(c_50605,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47712,c_50585])).

tff(c_50607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47590,c_50605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.29/5.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.29/5.82  
% 13.29/5.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.29/5.82  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > o_2_1_setfam_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 13.29/5.82  
% 13.29/5.82  %Foreground sorts:
% 13.29/5.82  
% 13.29/5.82  
% 13.29/5.82  %Background operators:
% 13.29/5.82  
% 13.29/5.82  
% 13.29/5.82  %Foreground operators:
% 13.29/5.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.29/5.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.29/5.82  tff(o_2_1_setfam_1, type, o_2_1_setfam_1: ($i * $i) > $i).
% 13.29/5.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.29/5.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.29/5.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.29/5.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.29/5.82  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 13.29/5.82  tff('#skF_7', type, '#skF_7': $i).
% 13.29/5.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.29/5.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.29/5.82  tff('#skF_6', type, '#skF_6': $i).
% 13.29/5.82  tff('#skF_9', type, '#skF_9': $i).
% 13.29/5.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.29/5.82  tff('#skF_8', type, '#skF_8': $i).
% 13.29/5.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.29/5.82  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 13.29/5.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.29/5.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.29/5.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.29/5.82  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.29/5.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.29/5.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.29/5.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.29/5.82  
% 13.29/5.84  tff(f_125, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 13.29/5.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.29/5.84  tff(f_113, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 13.29/5.84  tff(f_75, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 13.29/5.84  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 13.29/5.84  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 13.29/5.84  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 13.29/5.84  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 13.29/5.84  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.29/5.84  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 13.29/5.84  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 13.29/5.84  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 13.29/5.84  tff(f_98, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 13.29/5.84  tff(c_64, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.29/5.84  tff(c_92, plain, (![B_45, A_46]: (~r2_hidden(B_45, A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.29/5.84  tff(c_100, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_64, c_92])).
% 13.29/5.84  tff(c_38290, plain, (![A_52679, B_52680]: (r2_hidden('#skF_5'(A_52679, B_52680), A_52679) | r1_tarski(B_52680, k1_setfam_1(A_52679)) | k1_xboole_0=A_52679)), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.29/5.84  tff(c_68, plain, (~r2_hidden('#skF_7', '#skF_9') | ~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.29/5.84  tff(c_103, plain, (~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_68])).
% 13.29/5.84  tff(c_78, plain, (![D_41]: (r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8')) | r2_hidden('#skF_7', D_41) | ~r2_hidden(D_41, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.29/5.84  tff(c_35101, plain, (![D_41]: (r2_hidden('#skF_7', D_41) | ~r2_hidden(D_41, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_103, c_78])).
% 13.29/5.84  tff(c_38324, plain, (![B_52680]: (r2_hidden('#skF_7', '#skF_5'('#skF_8', B_52680)) | r1_tarski(B_52680, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_38290, c_35101])).
% 13.29/5.84  tff(c_40284, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_38324])).
% 13.29/5.84  tff(c_46, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.29/5.84  tff(c_48, plain, (![A_25]: (k8_setfam_1(A_25, k1_xboole_0)=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.29/5.84  tff(c_80, plain, (![A_25]: (k8_setfam_1(A_25, k1_xboole_0)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 13.29/5.84  tff(c_40306, plain, (![A_25]: (k8_setfam_1(A_25, '#skF_8')=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_40284, c_80])).
% 13.29/5.84  tff(c_35181, plain, (![B_49925, A_49926]: (m1_subset_1(B_49925, A_49926) | ~r2_hidden(B_49925, A_49926) | v1_xboole_0(A_49926))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.29/5.84  tff(c_35199, plain, (m1_subset_1('#skF_7', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_64, c_35181])).
% 13.29/5.84  tff(c_35211, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_100, c_35199])).
% 13.29/5.84  tff(c_35737, plain, (![A_49971, B_49972]: (r2_hidden('#skF_5'(A_49971, B_49972), A_49971) | r1_tarski(B_49972, k1_setfam_1(A_49971)) | k1_xboole_0=A_49971)), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.29/5.84  tff(c_35771, plain, (![B_49972]: (r2_hidden('#skF_7', '#skF_5'('#skF_8', B_49972)) | r1_tarski(B_49972, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_35737, c_35101])).
% 13.29/5.84  tff(c_37649, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_35771])).
% 13.29/5.84  tff(c_37670, plain, (![A_25]: (k8_setfam_1(A_25, '#skF_8')=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_37649, c_80])).
% 13.29/5.84  tff(c_161, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.29/5.84  tff(c_184, plain, (~m1_subset_1('#skF_7', k8_setfam_1('#skF_6', '#skF_8')) | v1_xboole_0(k8_setfam_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_161, c_103])).
% 13.29/5.84  tff(c_35650, plain, (~m1_subset_1('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_184])).
% 13.29/5.84  tff(c_37781, plain, (~m1_subset_1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_37670, c_35650])).
% 13.29/5.84  tff(c_37787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35211, c_37781])).
% 13.29/5.84  tff(c_37789, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_35771])).
% 13.29/5.84  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.29/5.84  tff(c_35102, plain, (![D_49918]: (r2_hidden('#skF_7', D_49918) | ~r2_hidden(D_49918, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_103, c_78])).
% 13.29/5.84  tff(c_35114, plain, (r2_hidden('#skF_7', '#skF_1'('#skF_8')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_35102])).
% 13.29/5.84  tff(c_35120, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_35114])).
% 13.29/5.84  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.29/5.84  tff(c_35877, plain, (![A_49981, B_49982]: (~v1_xboole_0(A_49981) | r1_tarski(B_49982, k1_setfam_1(A_49981)) | k1_xboole_0=A_49981)), inference(resolution, [status(thm)], [c_35737, c_2])).
% 13.29/5.84  tff(c_28, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | ~r1_tarski(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.29/5.84  tff(c_35906, plain, (![A_17, A_49981]: (r2_hidden(A_17, k1_setfam_1(A_49981)) | ~v1_xboole_0(A_49981) | k1_xboole_0=A_49981)), inference(resolution, [status(thm)], [c_35877, c_28])).
% 13.29/5.84  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.29/5.84  tff(c_35430, plain, (![A_49944, B_49945]: (k6_setfam_1(A_49944, B_49945)=k1_setfam_1(B_49945) | ~m1_subset_1(B_49945, k1_zfmisc_1(k1_zfmisc_1(A_49944))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.29/5.84  tff(c_35450, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_35430])).
% 13.29/5.84  tff(c_38132, plain, (![A_52574, B_52575]: (k8_setfam_1(A_52574, B_52575)=k6_setfam_1(A_52574, B_52575) | k1_xboole_0=B_52575 | ~m1_subset_1(B_52575, k1_zfmisc_1(k1_zfmisc_1(A_52574))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.29/5.84  tff(c_38145, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_66, c_38132])).
% 13.29/5.84  tff(c_38155, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_35450, c_38145])).
% 13.29/5.84  tff(c_38156, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_37789, c_38155])).
% 13.29/5.84  tff(c_38164, plain, (~r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_38156, c_103])).
% 13.29/5.84  tff(c_38186, plain, (~v1_xboole_0('#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_35906, c_38164])).
% 13.29/5.84  tff(c_38198, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_35120, c_38186])).
% 13.29/5.84  tff(c_38200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37789, c_38198])).
% 13.29/5.84  tff(c_38201, plain, (v1_xboole_0(k8_setfam_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_184])).
% 13.29/5.84  tff(c_40379, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40306, c_38201])).
% 13.29/5.84  tff(c_40385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_40379])).
% 13.29/5.84  tff(c_40387, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_38324])).
% 13.29/5.84  tff(c_40388, plain, (![A_55176, B_55177]: (k8_setfam_1(A_55176, B_55177)=k6_setfam_1(A_55176, B_55177) | k1_xboole_0=B_55177 | ~m1_subset_1(B_55177, k1_zfmisc_1(k1_zfmisc_1(A_55176))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.29/5.84  tff(c_40401, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_66, c_40388])).
% 13.29/5.84  tff(c_40411, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_35450, c_40401])).
% 13.29/5.84  tff(c_40417, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_40387, c_40411])).
% 13.29/5.84  tff(c_40419, plain, (v1_xboole_0(k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_40417, c_38201])).
% 13.29/5.84  tff(c_38430, plain, (![A_52689, B_52690]: (~v1_xboole_0(A_52689) | r1_tarski(B_52690, k1_setfam_1(A_52689)) | k1_xboole_0=A_52689)), inference(resolution, [status(thm)], [c_38290, c_2])).
% 13.29/5.84  tff(c_35277, plain, (![C_49934, B_49935, A_49936]: (r2_hidden(C_49934, B_49935) | ~r2_hidden(C_49934, A_49936) | ~r1_tarski(A_49936, B_49935))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.29/5.84  tff(c_35330, plain, (![B_49940]: (r2_hidden('#skF_7', B_49940) | ~r1_tarski('#skF_6', B_49940))), inference(resolution, [status(thm)], [c_64, c_35277])).
% 13.29/5.84  tff(c_35369, plain, (![B_49940]: (~v1_xboole_0(B_49940) | ~r1_tarski('#skF_6', B_49940))), inference(resolution, [status(thm)], [c_35330, c_2])).
% 13.29/5.84  tff(c_38458, plain, (![A_52689]: (~v1_xboole_0(k1_setfam_1(A_52689)) | ~v1_xboole_0(A_52689) | k1_xboole_0=A_52689)), inference(resolution, [status(thm)], [c_38430, c_35369])).
% 13.29/5.84  tff(c_40430, plain, (~v1_xboole_0('#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_40419, c_38458])).
% 13.29/5.84  tff(c_40433, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_35120, c_40430])).
% 13.29/5.84  tff(c_40435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40387, c_40433])).
% 13.29/5.84  tff(c_40437, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_35114])).
% 13.29/5.84  tff(c_41022, plain, (![A_55303, B_55304]: (r2_hidden('#skF_5'(A_55303, B_55304), A_55303) | r1_tarski(B_55304, k1_setfam_1(A_55303)) | k1_xboole_0=A_55303)), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.29/5.84  tff(c_41051, plain, (![B_55304]: (r2_hidden('#skF_7', '#skF_5'('#skF_8', B_55304)) | r1_tarski(B_55304, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_41022, c_35101])).
% 13.29/5.84  tff(c_43215, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_41051])).
% 13.29/5.84  tff(c_14, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.29/5.84  tff(c_99, plain, (![C_14]: (~v1_xboole_0(k1_tarski(C_14)))), inference(resolution, [status(thm)], [c_14, c_92])).
% 13.29/5.84  tff(c_40442, plain, (![A_55258, B_55259]: (k4_xboole_0(k1_tarski(A_55258), B_55259)=k1_xboole_0 | ~r2_hidden(A_55258, B_55259))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.29/5.84  tff(c_34, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.29/5.84  tff(c_40544, plain, (![C_55265, A_55266]: (~r2_hidden(C_55265, k1_xboole_0) | ~r2_hidden(A_55266, k1_tarski(C_55265)))), inference(superposition, [status(thm), theory('equality')], [c_40442, c_34])).
% 13.29/5.84  tff(c_40556, plain, (![C_55265]: (~r2_hidden(C_55265, k1_xboole_0) | v1_xboole_0(k1_tarski(C_55265)))), inference(resolution, [status(thm)], [c_4, c_40544])).
% 13.29/5.84  tff(c_40568, plain, (![C_55267]: (~r2_hidden(C_55267, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_99, c_40556])).
% 13.29/5.84  tff(c_40583, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_40568])).
% 13.29/5.84  tff(c_43232, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_43215, c_40583])).
% 13.29/5.84  tff(c_43239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40437, c_43232])).
% 13.29/5.84  tff(c_43241, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_41051])).
% 13.29/5.84  tff(c_40941, plain, (![A_55297, B_55298]: (k6_setfam_1(A_55297, B_55298)=k1_setfam_1(B_55298) | ~m1_subset_1(B_55298, k1_zfmisc_1(k1_zfmisc_1(A_55297))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.29/5.84  tff(c_40961, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_40941])).
% 13.29/5.84  tff(c_43488, plain, (![A_58117, B_58118]: (k8_setfam_1(A_58117, B_58118)=k6_setfam_1(A_58117, B_58118) | k1_xboole_0=B_58118 | ~m1_subset_1(B_58118, k1_zfmisc_1(k1_zfmisc_1(A_58117))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.29/5.84  tff(c_43501, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_66, c_43488])).
% 13.29/5.84  tff(c_43511, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_40961, c_43501])).
% 13.29/5.84  tff(c_43512, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_43241, c_43511])).
% 13.29/5.84  tff(c_43521, plain, (~r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_43512, c_103])).
% 13.29/5.84  tff(c_43240, plain, (![B_55304]: (r2_hidden('#skF_7', '#skF_5'('#skF_8', B_55304)) | r1_tarski(B_55304, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_41051])).
% 13.29/5.84  tff(c_30, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.29/5.84  tff(c_42029, plain, (![B_57537, A_57538]: (~r1_tarski(B_57537, '#skF_5'(A_57538, B_57537)) | r1_tarski(B_57537, k1_setfam_1(A_57538)) | k1_xboole_0=A_57538)), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.29/5.84  tff(c_47445, plain, (![A_60759, A_60760]: (r1_tarski(k1_tarski(A_60759), k1_setfam_1(A_60760)) | k1_xboole_0=A_60760 | ~r2_hidden(A_60759, '#skF_5'(A_60760, k1_tarski(A_60759))))), inference(resolution, [status(thm)], [c_30, c_42029])).
% 13.29/5.84  tff(c_47457, plain, (k1_xboole_0='#skF_8' | r1_tarski(k1_tarski('#skF_7'), k1_setfam_1('#skF_8'))), inference(resolution, [status(thm)], [c_43240, c_47445])).
% 13.29/5.84  tff(c_47504, plain, (r1_tarski(k1_tarski('#skF_7'), k1_setfam_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_43241, c_47457])).
% 13.29/5.84  tff(c_47525, plain, (r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(resolution, [status(thm)], [c_47504, c_28])).
% 13.29/5.84  tff(c_47589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43521, c_47525])).
% 13.29/5.84  tff(c_47590, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 13.29/5.84  tff(c_47700, plain, (![A_60824, B_60825]: (r2_hidden('#skF_2'(A_60824, B_60825), A_60824) | r1_tarski(A_60824, B_60825))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.29/5.84  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.29/5.84  tff(c_47712, plain, (![A_60824]: (r1_tarski(A_60824, A_60824))), inference(resolution, [status(thm)], [c_47700, c_8])).
% 13.29/5.84  tff(c_47591, plain, (r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_68])).
% 13.29/5.84  tff(c_70, plain, (r2_hidden('#skF_9', '#skF_8') | ~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.29/5.84  tff(c_47597, plain, (r2_hidden('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_47591, c_70])).
% 13.29/5.84  tff(c_47885, plain, (![C_60842, B_60843, A_60844]: (r2_hidden(C_60842, B_60843) | ~r2_hidden(C_60842, A_60844) | ~r1_tarski(A_60844, B_60843))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.29/5.84  tff(c_47903, plain, (![B_60843]: (r2_hidden('#skF_9', B_60843) | ~r1_tarski('#skF_8', B_60843))), inference(resolution, [status(thm)], [c_47597, c_47885])).
% 13.29/5.84  tff(c_56, plain, (![B_32, A_31]: (r1_tarski(k1_setfam_1(B_32), A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.29/5.84  tff(c_48039, plain, (![A_60853, B_60854]: (k6_setfam_1(A_60853, B_60854)=k1_setfam_1(B_60854) | ~m1_subset_1(B_60854, k1_zfmisc_1(k1_zfmisc_1(A_60853))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.29/5.84  tff(c_48059, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_48039])).
% 13.29/5.84  tff(c_50395, plain, (![A_63320, B_63321]: (k8_setfam_1(A_63320, B_63321)=k6_setfam_1(A_63320, B_63321) | k1_xboole_0=B_63321 | ~m1_subset_1(B_63321, k1_zfmisc_1(k1_zfmisc_1(A_63320))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.29/5.84  tff(c_50408, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_66, c_50395])).
% 13.29/5.84  tff(c_50418, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48059, c_50408])).
% 13.29/5.84  tff(c_50422, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_50418])).
% 13.29/5.84  tff(c_47907, plain, (![B_60845]: (r2_hidden('#skF_9', B_60845) | ~r1_tarski('#skF_8', B_60845))), inference(resolution, [status(thm)], [c_47597, c_47885])).
% 13.29/5.84  tff(c_47722, plain, (![A_60827, B_60828]: (k4_xboole_0(k1_tarski(A_60827), B_60828)=k1_xboole_0 | ~r2_hidden(A_60827, B_60828))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.29/5.84  tff(c_47745, plain, (![C_60831, A_60832]: (~r2_hidden(C_60831, k1_xboole_0) | ~r2_hidden(A_60832, k1_tarski(C_60831)))), inference(superposition, [status(thm), theory('equality')], [c_47722, c_34])).
% 13.29/5.84  tff(c_47757, plain, (![C_60831]: (~r2_hidden(C_60831, k1_xboole_0) | v1_xboole_0(k1_tarski(C_60831)))), inference(resolution, [status(thm)], [c_4, c_47745])).
% 13.29/5.84  tff(c_47767, plain, (![C_60831]: (~r2_hidden(C_60831, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_99, c_47757])).
% 13.29/5.84  tff(c_47935, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_47907, c_47767])).
% 13.29/5.84  tff(c_50438, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50422, c_47935])).
% 13.29/5.84  tff(c_50448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47712, c_50438])).
% 13.29/5.84  tff(c_50449, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(splitRight, [status(thm)], [c_50418])).
% 13.29/5.84  tff(c_47904, plain, (![B_60843]: (r2_hidden('#skF_7', B_60843) | ~r1_tarski(k8_setfam_1('#skF_6', '#skF_8'), B_60843))), inference(resolution, [status(thm)], [c_47591, c_47885])).
% 13.29/5.84  tff(c_50548, plain, (![B_63524]: (r2_hidden('#skF_7', B_63524) | ~r1_tarski(k1_setfam_1('#skF_8'), B_63524))), inference(demodulation, [status(thm), theory('equality')], [c_50449, c_47904])).
% 13.29/5.84  tff(c_50570, plain, (![A_63545]: (r2_hidden('#skF_7', A_63545) | ~r2_hidden(A_63545, '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_50548])).
% 13.29/5.84  tff(c_50585, plain, (r2_hidden('#skF_7', '#skF_9') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_47903, c_50570])).
% 13.29/5.84  tff(c_50605, plain, (r2_hidden('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_47712, c_50585])).
% 13.29/5.84  tff(c_50607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47590, c_50605])).
% 13.29/5.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.29/5.84  
% 13.29/5.84  Inference rules
% 13.29/5.84  ----------------------
% 13.29/5.84  #Ref     : 0
% 13.29/5.84  #Sup     : 8726
% 13.29/5.84  #Fact    : 0
% 13.29/5.84  #Define  : 0
% 13.29/5.84  #Split   : 123
% 13.29/5.85  #Chain   : 0
% 13.29/5.85  #Close   : 0
% 13.29/5.85  
% 13.29/5.85  Ordering : KBO
% 13.29/5.85  
% 13.29/5.85  Simplification rules
% 13.29/5.85  ----------------------
% 13.29/5.85  #Subsume      : 2565
% 13.29/5.85  #Demod        : 1468
% 13.29/5.85  #Tautology    : 1542
% 13.29/5.85  #SimpNegUnit  : 1255
% 13.29/5.85  #BackRed      : 315
% 13.29/5.85  
% 13.29/5.85  #Partial instantiations: 43915
% 13.29/5.85  #Strategies tried      : 1
% 13.29/5.85  
% 13.29/5.85  Timing (in seconds)
% 13.29/5.85  ----------------------
% 13.29/5.85  Preprocessing        : 0.34
% 13.29/5.85  Parsing              : 0.17
% 13.29/5.85  CNF conversion       : 0.03
% 13.29/5.85  Main loop            : 4.74
% 13.29/5.85  Inferencing          : 1.76
% 13.29/5.85  Reduction            : 1.37
% 13.29/5.85  Demodulation         : 0.83
% 13.29/5.85  BG Simplification    : 0.13
% 13.29/5.85  Subsumption          : 1.11
% 13.29/5.85  Abstraction          : 0.17
% 13.29/5.85  MUC search           : 0.00
% 13.29/5.85  Cooper               : 0.00
% 13.29/5.85  Total                : 5.13
% 13.29/5.85  Index Insertion      : 0.00
% 13.29/5.85  Index Deletion       : 0.00
% 13.29/5.85  Index Matching       : 0.00
% 13.29/5.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
