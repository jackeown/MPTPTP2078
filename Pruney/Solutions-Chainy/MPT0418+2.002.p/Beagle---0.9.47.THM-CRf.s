%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:50 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 143 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 247 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
            <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_38,plain,
    ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_63,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_186,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k7_setfam_1(A_46,B_47),k1_zfmisc_1(k1_zfmisc_1(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,B_6)) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(k1_zfmisc_1(A_46),k3_subset_1(k1_zfmisc_1(A_46),k7_setfam_1(A_46,B_47))) = k7_setfam_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(resolution,[status(thm)],[c_186,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k3_subset_1(A_1,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_468,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(k1_zfmisc_1(A_75),k7_setfam_1(A_75,B_76)) = k3_subset_1(k1_zfmisc_1(A_75),k7_setfam_1(A_75,B_76))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(resolution,[status(thm)],[c_186,c_2])).

tff(c_489,plain,(
    k4_xboole_0(k1_zfmisc_1('#skF_2'),k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1(k1_zfmisc_1('#skF_2'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_468])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] : m1_subset_1(k6_subset_1(A_3,B_4),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_3,B_4] : m1_subset_1(k4_xboole_0(A_3,B_4),k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4])).

tff(c_50,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k3_subset_1(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_203,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_subset_1(A_49,k4_xboole_0(A_49,B_50)) ),
    inference(resolution,[status(thm)],[c_39,c_50])).

tff(c_215,plain,(
    ! [A_49,B_50] : m1_subset_1(k3_subset_1(A_49,k4_xboole_0(A_49,B_50)),k1_zfmisc_1(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_39])).

tff(c_502,plain,(
    m1_subset_1(k3_subset_1(k1_zfmisc_1('#skF_2'),k3_subset_1(k1_zfmisc_1('#skF_2'),k7_setfam_1('#skF_2','#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_215])).

tff(c_622,plain,
    ( m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_502])).

tff(c_628,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_622])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_50])).

tff(c_67,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_39])).

tff(c_113,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(A_37,k3_subset_1(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_451,plain,(
    ! [D_72,A_73,B_74] :
      ( r2_hidden(D_72,k7_setfam_1(A_73,B_74))
      | ~ r2_hidden(k3_subset_1(A_73,D_72),B_74)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(k7_setfam_1(A_73,B_74),k1_zfmisc_1(k1_zfmisc_1(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_461,plain,(
    ! [B_74] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_74))
      | ~ r2_hidden('#skF_4',B_74)
      | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2',B_74),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_451])).

tff(c_2684,plain,(
    ! [B_148] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_148))
      | ~ r2_hidden('#skF_4',B_148)
      | ~ m1_subset_1(k7_setfam_1('#skF_2',B_148),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_461])).

tff(c_2720,plain,
    ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_628,c_2684])).

tff(c_2759,plain,(
    r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_63,c_2720])).

tff(c_2761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2759])).

tff(c_2763,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2767,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_39])).

tff(c_2762,plain,(
    r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2803,plain,(
    ! [A_153,B_154] :
      ( k3_subset_1(A_153,k3_subset_1(A_153,B_154)) = B_154
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2818,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_2803])).

tff(c_2878,plain,(
    ! [A_164,B_165] :
      ( m1_subset_1(k7_setfam_1(A_164,B_165),k1_zfmisc_1(k1_zfmisc_1(A_164)))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(k1_zfmisc_1(A_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3232,plain,(
    ! [A_194,B_195] :
      ( k3_subset_1(k1_zfmisc_1(A_194),k3_subset_1(k1_zfmisc_1(A_194),k7_setfam_1(A_194,B_195))) = k7_setfam_1(A_194,B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k1_zfmisc_1(A_194))) ) ),
    inference(resolution,[status(thm)],[c_2878,c_6])).

tff(c_3134,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(k1_zfmisc_1(A_187),k7_setfam_1(A_187,B_188)) = k3_subset_1(k1_zfmisc_1(A_187),k7_setfam_1(A_187,B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k1_zfmisc_1(A_187))) ) ),
    inference(resolution,[status(thm)],[c_2878,c_2])).

tff(c_3155,plain,(
    k4_xboole_0(k1_zfmisc_1('#skF_2'),k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1(k1_zfmisc_1('#skF_2'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_3134])).

tff(c_2921,plain,(
    ! [A_168,B_169] : k4_xboole_0(A_168,k4_xboole_0(A_168,B_169)) = k3_subset_1(A_168,k4_xboole_0(A_168,B_169)) ),
    inference(resolution,[status(thm)],[c_39,c_50])).

tff(c_2936,plain,(
    ! [A_168,B_169] : m1_subset_1(k3_subset_1(A_168,k4_xboole_0(A_168,B_169)),k1_zfmisc_1(A_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2921,c_39])).

tff(c_3165,plain,(
    m1_subset_1(k3_subset_1(k1_zfmisc_1('#skF_2'),k3_subset_1(k1_zfmisc_1('#skF_2'),k7_setfam_1('#skF_2','#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3155,c_2936])).

tff(c_3243,plain,
    ( m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3232,c_3165])).

tff(c_3251,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3243])).

tff(c_22,plain,(
    ! [A_9,D_19,B_10] :
      ( r2_hidden(k3_subset_1(A_9,D_19),B_10)
      | ~ r2_hidden(D_19,k7_setfam_1(A_9,B_10))
      | ~ m1_subset_1(D_19,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(k7_setfam_1(A_9,B_10),k1_zfmisc_1(k1_zfmisc_1(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3256,plain,(
    ! [D_19] :
      ( r2_hidden(k3_subset_1('#skF_2',D_19),'#skF_3')
      | ~ r2_hidden(D_19,k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_19,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_3251,c_22])).

tff(c_3342,plain,(
    ! [D_197] :
      ( r2_hidden(k3_subset_1('#skF_2',D_197),'#skF_3')
      | ~ r2_hidden(D_197,k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_197,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3256])).

tff(c_3359,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2818,c_3342])).

tff(c_3368,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2767,c_2762,c_3359])).

tff(c_3370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2763,c_3368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:48:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.22/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.98  
% 5.22/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.98  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.22/1.98  
% 5.22/1.98  %Foreground sorts:
% 5.22/1.98  
% 5.22/1.98  
% 5.22/1.98  %Background operators:
% 5.22/1.98  
% 5.22/1.98  
% 5.22/1.98  %Foreground operators:
% 5.22/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.22/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.22/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.22/1.98  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 5.22/1.98  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.22/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.22/1.98  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.22/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.22/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.22/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.22/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.22/1.98  
% 5.35/1.99  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 5.35/1.99  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 5.35/1.99  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.35/1.99  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.35/1.99  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.35/1.99  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.35/1.99  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 5.35/1.99  tff(c_38, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.35/1.99  tff(c_63, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 5.35/1.99  tff(c_32, plain, (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.35/1.99  tff(c_76, plain, (~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_32])).
% 5.35/1.99  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.35/1.99  tff(c_186, plain, (![A_46, B_47]: (m1_subset_1(k7_setfam_1(A_46, B_47), k1_zfmisc_1(k1_zfmisc_1(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/1.99  tff(c_6, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, B_6))=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.35/1.99  tff(c_194, plain, (![A_46, B_47]: (k3_subset_1(k1_zfmisc_1(A_46), k3_subset_1(k1_zfmisc_1(A_46), k7_setfam_1(A_46, B_47)))=k7_setfam_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(resolution, [status(thm)], [c_186, c_6])).
% 5.35/1.99  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k3_subset_1(A_1, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.35/1.99  tff(c_468, plain, (![A_75, B_76]: (k4_xboole_0(k1_zfmisc_1(A_75), k7_setfam_1(A_75, B_76))=k3_subset_1(k1_zfmisc_1(A_75), k7_setfam_1(A_75, B_76)) | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(resolution, [status(thm)], [c_186, c_2])).
% 5.35/1.99  tff(c_489, plain, (k4_xboole_0(k1_zfmisc_1('#skF_2'), k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1(k1_zfmisc_1('#skF_2'), k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_468])).
% 5.35/1.99  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.35/1.99  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(k6_subset_1(A_3, B_4), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.35/1.99  tff(c_39, plain, (![A_3, B_4]: (m1_subset_1(k4_xboole_0(A_3, B_4), k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4])).
% 5.35/1.99  tff(c_50, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k3_subset_1(A_30, B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.35/1.99  tff(c_203, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_subset_1(A_49, k4_xboole_0(A_49, B_50)))), inference(resolution, [status(thm)], [c_39, c_50])).
% 5.35/1.99  tff(c_215, plain, (![A_49, B_50]: (m1_subset_1(k3_subset_1(A_49, k4_xboole_0(A_49, B_50)), k1_zfmisc_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_39])).
% 5.35/1.99  tff(c_502, plain, (m1_subset_1(k3_subset_1(k1_zfmisc_1('#skF_2'), k3_subset_1(k1_zfmisc_1('#skF_2'), k7_setfam_1('#skF_2', '#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_489, c_215])).
% 5.35/1.99  tff(c_622, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_194, c_502])).
% 5.35/1.99  tff(c_628, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_622])).
% 5.35/1.99  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.35/1.99  tff(c_62, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_50])).
% 5.35/1.99  tff(c_67, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_39])).
% 5.35/1.99  tff(c_113, plain, (![A_37, B_38]: (k3_subset_1(A_37, k3_subset_1(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.35/1.99  tff(c_131, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_28, c_113])).
% 5.35/1.99  tff(c_451, plain, (![D_72, A_73, B_74]: (r2_hidden(D_72, k7_setfam_1(A_73, B_74)) | ~r2_hidden(k3_subset_1(A_73, D_72), B_74) | ~m1_subset_1(D_72, k1_zfmisc_1(A_73)) | ~m1_subset_1(k7_setfam_1(A_73, B_74), k1_zfmisc_1(k1_zfmisc_1(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.35/1.99  tff(c_461, plain, (![B_74]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_74)) | ~r2_hidden('#skF_4', B_74) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', B_74), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_131, c_451])).
% 5.35/1.99  tff(c_2684, plain, (![B_148]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_148)) | ~r2_hidden('#skF_4', B_148) | ~m1_subset_1(k7_setfam_1('#skF_2', B_148), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_148, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_461])).
% 5.35/1.99  tff(c_2720, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_628, c_2684])).
% 5.35/1.99  tff(c_2759, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_63, c_2720])).
% 5.35/1.99  tff(c_2761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2759])).
% 5.35/1.99  tff(c_2763, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 5.35/1.99  tff(c_2767, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_39])).
% 5.35/1.99  tff(c_2762, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_38])).
% 5.35/1.99  tff(c_2803, plain, (![A_153, B_154]: (k3_subset_1(A_153, k3_subset_1(A_153, B_154))=B_154 | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.35/1.99  tff(c_2818, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_28, c_2803])).
% 5.35/1.99  tff(c_2878, plain, (![A_164, B_165]: (m1_subset_1(k7_setfam_1(A_164, B_165), k1_zfmisc_1(k1_zfmisc_1(A_164))) | ~m1_subset_1(B_165, k1_zfmisc_1(k1_zfmisc_1(A_164))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/1.99  tff(c_3232, plain, (![A_194, B_195]: (k3_subset_1(k1_zfmisc_1(A_194), k3_subset_1(k1_zfmisc_1(A_194), k7_setfam_1(A_194, B_195)))=k7_setfam_1(A_194, B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(k1_zfmisc_1(A_194))))), inference(resolution, [status(thm)], [c_2878, c_6])).
% 5.35/1.99  tff(c_3134, plain, (![A_187, B_188]: (k4_xboole_0(k1_zfmisc_1(A_187), k7_setfam_1(A_187, B_188))=k3_subset_1(k1_zfmisc_1(A_187), k7_setfam_1(A_187, B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1(k1_zfmisc_1(A_187))))), inference(resolution, [status(thm)], [c_2878, c_2])).
% 5.35/1.99  tff(c_3155, plain, (k4_xboole_0(k1_zfmisc_1('#skF_2'), k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1(k1_zfmisc_1('#skF_2'), k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_3134])).
% 5.35/1.99  tff(c_2921, plain, (![A_168, B_169]: (k4_xboole_0(A_168, k4_xboole_0(A_168, B_169))=k3_subset_1(A_168, k4_xboole_0(A_168, B_169)))), inference(resolution, [status(thm)], [c_39, c_50])).
% 5.35/1.99  tff(c_2936, plain, (![A_168, B_169]: (m1_subset_1(k3_subset_1(A_168, k4_xboole_0(A_168, B_169)), k1_zfmisc_1(A_168)))), inference(superposition, [status(thm), theory('equality')], [c_2921, c_39])).
% 5.35/1.99  tff(c_3165, plain, (m1_subset_1(k3_subset_1(k1_zfmisc_1('#skF_2'), k3_subset_1(k1_zfmisc_1('#skF_2'), k7_setfam_1('#skF_2', '#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3155, c_2936])).
% 5.35/1.99  tff(c_3243, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3232, c_3165])).
% 5.35/1.99  tff(c_3251, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3243])).
% 5.35/1.99  tff(c_22, plain, (![A_9, D_19, B_10]: (r2_hidden(k3_subset_1(A_9, D_19), B_10) | ~r2_hidden(D_19, k7_setfam_1(A_9, B_10)) | ~m1_subset_1(D_19, k1_zfmisc_1(A_9)) | ~m1_subset_1(k7_setfam_1(A_9, B_10), k1_zfmisc_1(k1_zfmisc_1(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.35/1.99  tff(c_3256, plain, (![D_19]: (r2_hidden(k3_subset_1('#skF_2', D_19), '#skF_3') | ~r2_hidden(D_19, k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_19, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_3251, c_22])).
% 5.35/1.99  tff(c_3342, plain, (![D_197]: (r2_hidden(k3_subset_1('#skF_2', D_197), '#skF_3') | ~r2_hidden(D_197, k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_197, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3256])).
% 5.35/1.99  tff(c_3359, plain, (r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2818, c_3342])).
% 5.35/1.99  tff(c_3368, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2767, c_2762, c_3359])).
% 5.35/1.99  tff(c_3370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2763, c_3368])).
% 5.35/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/1.99  
% 5.35/1.99  Inference rules
% 5.35/1.99  ----------------------
% 5.35/1.99  #Ref     : 0
% 5.35/1.99  #Sup     : 839
% 5.35/1.99  #Fact    : 0
% 5.35/1.99  #Define  : 0
% 5.35/1.99  #Split   : 8
% 5.35/1.99  #Chain   : 0
% 5.35/1.99  #Close   : 0
% 5.35/1.99  
% 5.35/1.99  Ordering : KBO
% 5.35/1.99  
% 5.35/1.99  Simplification rules
% 5.35/1.99  ----------------------
% 5.35/1.99  #Subsume      : 86
% 5.35/1.99  #Demod        : 420
% 5.35/1.99  #Tautology    : 237
% 5.35/1.99  #SimpNegUnit  : 6
% 5.35/1.99  #BackRed      : 30
% 5.35/1.99  
% 5.35/1.99  #Partial instantiations: 0
% 5.35/1.99  #Strategies tried      : 1
% 5.35/1.99  
% 5.35/1.99  Timing (in seconds)
% 5.35/1.99  ----------------------
% 5.35/2.00  Preprocessing        : 0.28
% 5.35/2.00  Parsing              : 0.15
% 5.35/2.00  CNF conversion       : 0.02
% 5.35/2.00  Main loop            : 0.89
% 5.35/2.00  Inferencing          : 0.28
% 5.35/2.00  Reduction            : 0.31
% 5.35/2.00  Demodulation         : 0.23
% 5.35/2.00  BG Simplification    : 0.04
% 5.35/2.00  Subsumption          : 0.18
% 5.35/2.00  Abstraction          : 0.06
% 5.35/2.00  MUC search           : 0.00
% 5.35/2.00  Cooper               : 0.00
% 5.35/2.00  Total                : 1.21
% 5.35/2.00  Index Insertion      : 0.00
% 5.35/2.00  Index Deletion       : 0.00
% 5.35/2.00  Index Matching       : 0.00
% 5.35/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
