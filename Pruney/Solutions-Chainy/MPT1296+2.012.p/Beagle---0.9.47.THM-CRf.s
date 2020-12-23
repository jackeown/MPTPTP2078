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
% DateTime   : Thu Dec  3 10:22:42 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 249 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  117 ( 505 expanded)
%              Number of equality atoms :   37 ( 181 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_88,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_44,plain,(
    k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) != k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_2'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_121,plain,(
    ! [A_62,C_63,B_64] :
      ( m1_subset_1(A_62,C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_126,plain,(
    ! [A_62] :
      ( m1_subset_1(A_62,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_121])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [B_56,A_57] :
      ( ~ r2_hidden(B_56,A_57)
      | k4_xboole_0(A_57,k1_tarski(B_56)) != A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_95,plain,(
    ! [B_56] : ~ r2_hidden(B_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k7_setfam_1(A_22,B_23),k1_zfmisc_1(k1_zfmisc_1(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,(
    ! [A_66,B_67] :
      ( k7_setfam_1(A_66,k7_setfam_1(A_66,B_67)) = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_141,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_135])).

tff(c_202,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k7_setfam_1(A_75,B_76),k1_zfmisc_1(k1_zfmisc_1(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_26,C_28,B_27] :
      ( m1_subset_1(A_26,C_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(C_28))
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_235,plain,(
    ! [A_98,A_99,B_100] :
      ( m1_subset_1(A_98,k1_zfmisc_1(A_99))
      | ~ r2_hidden(A_98,k7_setfam_1(A_99,B_100))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k1_zfmisc_1(A_99))) ) ),
    inference(resolution,[status(thm)],[c_202,c_34])).

tff(c_386,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1('#skF_2'(k7_setfam_1(A_113,B_114)),k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(A_113)))
      | k7_setfam_1(A_113,B_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_235])).

tff(c_408,plain,
    ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_386])).

tff(c_416,plain,
    ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_408])).

tff(c_417,plain,
    ( m1_subset_1('#skF_2'('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_416])).

tff(c_418,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_421,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_30,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_421])).

tff(c_427,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_1075,plain,(
    ! [A_145] :
      ( m1_subset_1(A_145,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_145,k7_setfam_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_427,c_34])).

tff(c_1080,plain,
    ( m1_subset_1('#skF_2'(k7_setfam_1('#skF_3','#skF_4')),k1_zfmisc_1('#skF_3'))
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1075])).

tff(c_1081,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_1085,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_141])).

tff(c_1137,plain,(
    ! [A_146,D_147,B_148] :
      ( r2_hidden(k3_subset_1(A_146,D_147),B_148)
      | ~ r2_hidden(D_147,k7_setfam_1(A_146,B_148))
      | ~ m1_subset_1(D_147,k1_zfmisc_1(A_146))
      | ~ m1_subset_1(k7_setfam_1(A_146,B_148),k1_zfmisc_1(k1_zfmisc_1(A_146)))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k1_zfmisc_1(A_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1139,plain,(
    ! [D_147] :
      ( r2_hidden(k3_subset_1('#skF_3',D_147),k1_xboole_0)
      | ~ r2_hidden(D_147,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_147,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_1137])).

tff(c_1147,plain,(
    ! [D_147] :
      ( r2_hidden(k3_subset_1('#skF_3',D_147),k1_xboole_0)
      | ~ r2_hidden(D_147,'#skF_4')
      | ~ m1_subset_1(D_147,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48,c_1085,c_1139])).

tff(c_1154,plain,(
    ! [D_149] :
      ( ~ r2_hidden(D_149,'#skF_4')
      | ~ m1_subset_1(D_149,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_1147])).

tff(c_1188,plain,(
    ! [A_150] : ~ r2_hidden(A_150,'#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_1154])).

tff(c_1192,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_1188])).

tff(c_1196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1192])).

tff(c_1198,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_42,plain,(
    ! [A_47,B_48] :
      ( k6_setfam_1(A_47,k7_setfam_1(A_47,B_48)) = k3_subset_1(A_47,k5_setfam_1(A_47,B_48))
      | k1_xboole_0 = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_439,plain,
    ( k6_setfam_1('#skF_3',k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')))
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_427,c_42])).

tff(c_450,plain,
    ( k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4')
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_439])).

tff(c_1575,plain,(
    k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1198,c_450])).

tff(c_191,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k5_setfam_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_subset_1(A_6,k3_subset_1(A_6,B_7)) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_201,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,k5_setfam_1(A_73,B_74))) = k5_setfam_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(resolution,[status(thm)],[c_191,c_10])).

tff(c_446,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')))) = k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_427,c_201])).

tff(c_1576,plain,(
    k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1575,c_446])).

tff(c_1578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1576])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.81  
% 4.00/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.81  %$ r2_hidden > m1_subset_1 > k4_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.00/1.81  
% 4.00/1.81  %Foreground sorts:
% 4.00/1.81  
% 4.00/1.81  
% 4.00/1.81  %Background operators:
% 4.00/1.81  
% 4.00/1.81  
% 4.00/1.81  %Foreground operators:
% 4.00/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.00/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.00/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.00/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.00/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.00/1.81  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.00/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.00/1.81  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.00/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.00/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.81  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.00/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.00/1.81  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.00/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.00/1.81  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.00/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.81  
% 4.00/1.83  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 4.00/1.83  tff(f_88, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 4.00/1.83  tff(f_72, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.00/1.83  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.00/1.83  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.00/1.83  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.00/1.83  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.00/1.83  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.00/1.83  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 4.00/1.83  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 4.00/1.83  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.00/1.83  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.00/1.83  tff(c_44, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))!=k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.00/1.83  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.00/1.83  tff(c_36, plain, (![A_29]: (r2_hidden('#skF_2'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.00/1.83  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.00/1.83  tff(c_121, plain, (![A_62, C_63, B_64]: (m1_subset_1(A_62, C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.00/1.83  tff(c_126, plain, (![A_62]: (m1_subset_1(A_62, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_121])).
% 4.00/1.83  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.00/1.83  tff(c_86, plain, (![B_56, A_57]: (~r2_hidden(B_56, A_57) | k4_xboole_0(A_57, k1_tarski(B_56))!=A_57)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.00/1.83  tff(c_95, plain, (![B_56]: (~r2_hidden(B_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_86])).
% 4.00/1.83  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.00/1.83  tff(c_30, plain, (![A_22, B_23]: (m1_subset_1(k7_setfam_1(A_22, B_23), k1_zfmisc_1(k1_zfmisc_1(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.00/1.83  tff(c_135, plain, (![A_66, B_67]: (k7_setfam_1(A_66, k7_setfam_1(A_66, B_67))=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.83  tff(c_141, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_48, c_135])).
% 4.00/1.83  tff(c_202, plain, (![A_75, B_76]: (m1_subset_1(k7_setfam_1(A_75, B_76), k1_zfmisc_1(k1_zfmisc_1(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.00/1.83  tff(c_34, plain, (![A_26, C_28, B_27]: (m1_subset_1(A_26, C_28) | ~m1_subset_1(B_27, k1_zfmisc_1(C_28)) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.00/1.83  tff(c_235, plain, (![A_98, A_99, B_100]: (m1_subset_1(A_98, k1_zfmisc_1(A_99)) | ~r2_hidden(A_98, k7_setfam_1(A_99, B_100)) | ~m1_subset_1(B_100, k1_zfmisc_1(k1_zfmisc_1(A_99))))), inference(resolution, [status(thm)], [c_202, c_34])).
% 4.00/1.83  tff(c_386, plain, (![A_113, B_114]: (m1_subset_1('#skF_2'(k7_setfam_1(A_113, B_114)), k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(A_113))) | k7_setfam_1(A_113, B_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_235])).
% 4.00/1.83  tff(c_408, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_141, c_386])).
% 4.00/1.83  tff(c_416, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_408])).
% 4.00/1.83  tff(c_417, plain, (m1_subset_1('#skF_2'('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_416])).
% 4.00/1.83  tff(c_418, plain, (~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_417])).
% 4.00/1.83  tff(c_421, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_30, c_418])).
% 4.00/1.83  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_421])).
% 4.00/1.83  tff(c_427, plain, (m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_417])).
% 4.00/1.83  tff(c_1075, plain, (![A_145]: (m1_subset_1(A_145, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_145, k7_setfam_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_427, c_34])).
% 4.00/1.83  tff(c_1080, plain, (m1_subset_1('#skF_2'(k7_setfam_1('#skF_3', '#skF_4')), k1_zfmisc_1('#skF_3')) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1075])).
% 4.00/1.83  tff(c_1081, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1080])).
% 4.00/1.83  tff(c_1085, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_141])).
% 4.00/1.83  tff(c_1137, plain, (![A_146, D_147, B_148]: (r2_hidden(k3_subset_1(A_146, D_147), B_148) | ~r2_hidden(D_147, k7_setfam_1(A_146, B_148)) | ~m1_subset_1(D_147, k1_zfmisc_1(A_146)) | ~m1_subset_1(k7_setfam_1(A_146, B_148), k1_zfmisc_1(k1_zfmisc_1(A_146))) | ~m1_subset_1(B_148, k1_zfmisc_1(k1_zfmisc_1(A_146))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.00/1.83  tff(c_1139, plain, (![D_147]: (r2_hidden(k3_subset_1('#skF_3', D_147), k1_xboole_0) | ~r2_hidden(D_147, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_147, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1085, c_1137])).
% 4.00/1.83  tff(c_1147, plain, (![D_147]: (r2_hidden(k3_subset_1('#skF_3', D_147), k1_xboole_0) | ~r2_hidden(D_147, '#skF_4') | ~m1_subset_1(D_147, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48, c_1085, c_1139])).
% 4.00/1.83  tff(c_1154, plain, (![D_149]: (~r2_hidden(D_149, '#skF_4') | ~m1_subset_1(D_149, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_95, c_1147])).
% 4.00/1.83  tff(c_1188, plain, (![A_150]: (~r2_hidden(A_150, '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_1154])).
% 4.00/1.83  tff(c_1192, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_1188])).
% 4.00/1.83  tff(c_1196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1192])).
% 4.00/1.83  tff(c_1198, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1080])).
% 4.00/1.83  tff(c_42, plain, (![A_47, B_48]: (k6_setfam_1(A_47, k7_setfam_1(A_47, B_48))=k3_subset_1(A_47, k5_setfam_1(A_47, B_48)) | k1_xboole_0=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.00/1.83  tff(c_439, plain, (k6_setfam_1('#skF_3', k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_427, c_42])).
% 4.00/1.83  tff(c_450, plain, (k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4') | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141, c_439])).
% 4.00/1.83  tff(c_1575, plain, (k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1198, c_450])).
% 4.00/1.83  tff(c_191, plain, (![A_73, B_74]: (m1_subset_1(k5_setfam_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.00/1.83  tff(c_10, plain, (![A_6, B_7]: (k3_subset_1(A_6, k3_subset_1(A_6, B_7))=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.00/1.83  tff(c_201, plain, (![A_73, B_74]: (k3_subset_1(A_73, k3_subset_1(A_73, k5_setfam_1(A_73, B_74)))=k5_setfam_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(resolution, [status(thm)], [c_191, c_10])).
% 4.00/1.83  tff(c_446, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))))=k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_427, c_201])).
% 4.00/1.83  tff(c_1576, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1575, c_446])).
% 4.00/1.83  tff(c_1578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1576])).
% 4.00/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.83  
% 4.00/1.83  Inference rules
% 4.00/1.83  ----------------------
% 4.00/1.83  #Ref     : 0
% 4.00/1.83  #Sup     : 367
% 4.00/1.83  #Fact    : 0
% 4.00/1.83  #Define  : 0
% 4.00/1.83  #Split   : 17
% 4.00/1.83  #Chain   : 0
% 4.00/1.83  #Close   : 0
% 4.00/1.83  
% 4.00/1.83  Ordering : KBO
% 4.00/1.83  
% 4.00/1.83  Simplification rules
% 4.00/1.83  ----------------------
% 4.00/1.83  #Subsume      : 48
% 4.00/1.83  #Demod        : 183
% 4.00/1.83  #Tautology    : 150
% 4.00/1.83  #SimpNegUnit  : 35
% 4.00/1.83  #BackRed      : 36
% 4.00/1.83  
% 4.00/1.83  #Partial instantiations: 0
% 4.00/1.83  #Strategies tried      : 1
% 4.00/1.83  
% 4.00/1.83  Timing (in seconds)
% 4.00/1.83  ----------------------
% 4.00/1.83  Preprocessing        : 0.34
% 4.00/1.83  Parsing              : 0.17
% 4.00/1.83  CNF conversion       : 0.02
% 4.00/1.83  Main loop            : 0.66
% 4.00/1.83  Inferencing          : 0.22
% 4.00/1.83  Reduction            : 0.23
% 4.00/1.83  Demodulation         : 0.15
% 4.00/1.83  BG Simplification    : 0.03
% 4.00/1.83  Subsumption          : 0.13
% 4.00/1.83  Abstraction          : 0.03
% 4.00/1.83  MUC search           : 0.00
% 4.00/1.83  Cooper               : 0.00
% 4.00/1.83  Total                : 1.04
% 4.00/1.83  Index Insertion      : 0.00
% 4.00/1.83  Index Deletion       : 0.00
% 4.00/1.83  Index Matching       : 0.00
% 4.00/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
