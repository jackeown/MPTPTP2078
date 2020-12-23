%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:34 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 318 expanded)
%              Number of leaves         :   30 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 (1186 expanded)
%              Number of equality atoms :   39 ( 128 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,k1_tarski(B))
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => r2_relset_1(A,k1_tarski(B),C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

tff(f_85,axiom,(
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

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_275,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( r2_hidden('#skF_3'(A_91,B_92,C_93,D_94),A_91)
      | r2_relset_1(A_91,B_92,C_93,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(D_94,A_91,B_92)
      | ~ v1_funct_1(D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(C_93,A_91,B_92)
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_277,plain,(
    ! [C_93] :
      ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),C_93,'#skF_7'),'#skF_4')
      | r2_relset_1('#skF_4',k1_tarski('#skF_5'),C_93,'#skF_7')
      | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
      | ~ v1_funct_2(C_93,'#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_46,c_275])).

tff(c_700,plain,(
    ! [C_1258] :
      ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),C_1258,'#skF_7'),'#skF_4')
      | r2_relset_1('#skF_4',k1_tarski('#skF_5'),C_1258,'#skF_7')
      | ~ m1_subset_1(C_1258,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
      | ~ v1_funct_2(C_1258,'#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1(C_1258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_277])).

tff(c_710,plain,
    ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4')
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_700])).

tff(c_717,plain,
    ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4')
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_710])).

tff(c_718,plain,(
    r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_717])).

tff(c_42,plain,(
    ! [D_31,C_30,B_29,A_28] :
      ( r2_hidden(k1_funct_1(D_31,C_30),B_29)
      | k1_xboole_0 = B_29
      | ~ r2_hidden(C_30,A_28)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(D_31,A_28,B_29)
      | ~ v1_funct_1(D_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_723,plain,(
    ! [D_1261,B_1262] :
      ( r2_hidden(k1_funct_1(D_1261,'#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')),B_1262)
      | k1_xboole_0 = B_1262
      | ~ m1_subset_1(D_1261,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1262)))
      | ~ v1_funct_2(D_1261,'#skF_4',B_1262)
      | ~ v1_funct_1(D_1261) ) ),
    inference(resolution,[status(thm)],[c_718,c_42])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_732,plain,(
    ! [D_1263,A_1264] :
      ( k1_funct_1(D_1263,'#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = A_1264
      | k1_tarski(A_1264) = k1_xboole_0
      | ~ m1_subset_1(D_1263,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski(A_1264))))
      | ~ v1_funct_2(D_1263,'#skF_4',k1_tarski(A_1264))
      | ~ v1_funct_1(D_1263) ) ),
    inference(resolution,[status(thm)],[c_723,c_4])).

tff(c_735,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_732])).

tff(c_745,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_735])).

tff(c_754,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_765,plain,(
    ~ r2_relset_1('#skF_4',k1_xboole_0,'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_44])).

tff(c_22,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k2_zfmisc_1(A_12,k1_tarski(B_13)) != k1_xboole_0
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_793,plain,(
    ! [A_12] :
      ( k2_zfmisc_1(A_12,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_12 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_26])).

tff(c_970,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_793])).

tff(c_814,plain,(
    ! [A_1269] : k1_xboole_0 = A_1269 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_793])).

tff(c_971,plain,(
    ! [A_1269] : A_1269 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_814])).

tff(c_145,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_relset_1(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_157,plain,(
    r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_760,plain,(
    r2_relset_1('#skF_4',k1_xboole_0,'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_157])).

tff(c_2871,plain,(
    r2_relset_1('#skF_4',k1_xboole_0,'#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_760])).

tff(c_2920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_2871])).

tff(c_2922,plain,(
    k1_tarski('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_2921,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_38,plain,(
    ! [D_26,A_20,B_21,C_22] :
      ( k1_funct_1(D_26,'#skF_3'(A_20,B_21,C_22,D_26)) != k1_funct_1(C_22,'#skF_3'(A_20,B_21,C_22,D_26))
      | r2_relset_1(A_20,B_21,C_22,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_26,A_20,B_21)
      | ~ v1_funct_1(D_26)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2925,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) != '#skF_5'
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2921,c_38])).

tff(c_2932,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) != '#skF_5'
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_2925])).

tff(c_2933,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2932])).

tff(c_742,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_732])).

tff(c_749,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_742])).

tff(c_2937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2922,c_2933,c_749])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.89  
% 4.62/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.89  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1
% 4.62/1.89  
% 4.62/1.89  %Foreground sorts:
% 4.62/1.89  
% 4.62/1.89  
% 4.62/1.89  %Background operators:
% 4.62/1.89  
% 4.62/1.89  
% 4.62/1.89  %Foreground operators:
% 4.62/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.62/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.62/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.62/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.62/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.62/1.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.62/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.62/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.89  
% 4.62/1.91  tff(f_113, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, k1_tarski(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r2_relset_1(A, k1_tarski(B), C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_2)).
% 4.62/1.91  tff(f_85, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.62/1.91  tff(f_97, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.62/1.91  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.62/1.91  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.62/1.91  tff(f_53, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 4.62/1.91  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.62/1.91  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.62/1.91  tff(c_48, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.62/1.91  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.62/1.91  tff(c_44, plain, (~r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.62/1.91  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.62/1.91  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.62/1.91  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.62/1.91  tff(c_275, plain, (![A_91, B_92, C_93, D_94]: (r2_hidden('#skF_3'(A_91, B_92, C_93, D_94), A_91) | r2_relset_1(A_91, B_92, C_93, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(D_94, A_91, B_92) | ~v1_funct_1(D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(C_93, A_91, B_92) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.62/1.91  tff(c_277, plain, (![C_93]: (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), C_93, '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), C_93, '#skF_7') | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2(C_93, '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1(C_93))), inference(resolution, [status(thm)], [c_46, c_275])).
% 4.62/1.91  tff(c_700, plain, (![C_1258]: (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), C_1258, '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), C_1258, '#skF_7') | ~m1_subset_1(C_1258, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2(C_1258, '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1(C_1258))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_277])).
% 4.62/1.91  tff(c_710, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_700])).
% 4.62/1.91  tff(c_717, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_710])).
% 4.62/1.91  tff(c_718, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_717])).
% 4.62/1.91  tff(c_42, plain, (![D_31, C_30, B_29, A_28]: (r2_hidden(k1_funct_1(D_31, C_30), B_29) | k1_xboole_0=B_29 | ~r2_hidden(C_30, A_28) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(D_31, A_28, B_29) | ~v1_funct_1(D_31))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.62/1.91  tff(c_723, plain, (![D_1261, B_1262]: (r2_hidden(k1_funct_1(D_1261, '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), B_1262) | k1_xboole_0=B_1262 | ~m1_subset_1(D_1261, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1262))) | ~v1_funct_2(D_1261, '#skF_4', B_1262) | ~v1_funct_1(D_1261))), inference(resolution, [status(thm)], [c_718, c_42])).
% 4.62/1.91  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.62/1.91  tff(c_732, plain, (![D_1263, A_1264]: (k1_funct_1(D_1263, '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))=A_1264 | k1_tarski(A_1264)=k1_xboole_0 | ~m1_subset_1(D_1263, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski(A_1264)))) | ~v1_funct_2(D_1263, '#skF_4', k1_tarski(A_1264)) | ~v1_funct_1(D_1263))), inference(resolution, [status(thm)], [c_723, c_4])).
% 4.62/1.91  tff(c_735, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_732])).
% 4.62/1.91  tff(c_745, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_735])).
% 4.62/1.91  tff(c_754, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_745])).
% 4.62/1.91  tff(c_765, plain, (~r2_relset_1('#skF_4', k1_xboole_0, '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_754, c_44])).
% 4.62/1.91  tff(c_22, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.62/1.91  tff(c_26, plain, (![A_12, B_13]: (k2_zfmisc_1(A_12, k1_tarski(B_13))!=k1_xboole_0 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.62/1.91  tff(c_793, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_12)), inference(superposition, [status(thm), theory('equality')], [c_754, c_26])).
% 4.62/1.91  tff(c_970, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_793])).
% 4.62/1.91  tff(c_814, plain, (![A_1269]: (k1_xboole_0=A_1269)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_793])).
% 4.62/1.91  tff(c_971, plain, (![A_1269]: (A_1269='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_970, c_814])).
% 4.62/1.91  tff(c_145, plain, (![A_54, B_55, D_56]: (r2_relset_1(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.62/1.91  tff(c_157, plain, (r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_46, c_145])).
% 4.62/1.91  tff(c_760, plain, (r2_relset_1('#skF_4', k1_xboole_0, '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_754, c_157])).
% 4.62/1.91  tff(c_2871, plain, (r2_relset_1('#skF_4', k1_xboole_0, '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_971, c_760])).
% 4.62/1.91  tff(c_2920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_765, c_2871])).
% 4.62/1.91  tff(c_2922, plain, (k1_tarski('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_745])).
% 4.62/1.91  tff(c_2921, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5'), inference(splitRight, [status(thm)], [c_745])).
% 4.62/1.91  tff(c_38, plain, (![D_26, A_20, B_21, C_22]: (k1_funct_1(D_26, '#skF_3'(A_20, B_21, C_22, D_26))!=k1_funct_1(C_22, '#skF_3'(A_20, B_21, C_22, D_26)) | r2_relset_1(A_20, B_21, C_22, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(D_26, A_20, B_21) | ~v1_funct_1(D_26) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.62/1.91  tff(c_2925, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))!='#skF_5' | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2921, c_38])).
% 5.02/1.91  tff(c_2932, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))!='#skF_5' | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_46, c_2925])).
% 5.02/1.91  tff(c_2933, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_44, c_2932])).
% 5.02/1.91  tff(c_742, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_732])).
% 5.02/1.91  tff(c_749, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_742])).
% 5.02/1.91  tff(c_2937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2922, c_2933, c_749])).
% 5.02/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.91  
% 5.02/1.91  Inference rules
% 5.02/1.91  ----------------------
% 5.02/1.91  #Ref     : 2
% 5.02/1.91  #Sup     : 975
% 5.02/1.91  #Fact    : 0
% 5.02/1.91  #Define  : 0
% 5.02/1.91  #Split   : 3
% 5.02/1.91  #Chain   : 0
% 5.02/1.91  #Close   : 0
% 5.02/1.91  
% 5.02/1.91  Ordering : KBO
% 5.02/1.91  
% 5.02/1.91  Simplification rules
% 5.02/1.91  ----------------------
% 5.02/1.91  #Subsume      : 81
% 5.02/1.91  #Demod        : 311
% 5.02/1.91  #Tautology    : 220
% 5.02/1.91  #SimpNegUnit  : 7
% 5.02/1.91  #BackRed      : 26
% 5.02/1.91  
% 5.02/1.91  #Partial instantiations: 1055
% 5.02/1.91  #Strategies tried      : 1
% 5.02/1.91  
% 5.02/1.91  Timing (in seconds)
% 5.02/1.91  ----------------------
% 5.02/1.91  Preprocessing        : 0.32
% 5.02/1.91  Parsing              : 0.16
% 5.02/1.91  CNF conversion       : 0.02
% 5.02/1.91  Main loop            : 0.80
% 5.02/1.91  Inferencing          : 0.32
% 5.02/1.91  Reduction            : 0.23
% 5.02/1.91  Demodulation         : 0.17
% 5.02/1.91  BG Simplification    : 0.03
% 5.02/1.91  Subsumption          : 0.15
% 5.02/1.91  Abstraction          : 0.04
% 5.02/1.91  MUC search           : 0.00
% 5.02/1.91  Cooper               : 0.00
% 5.02/1.91  Total                : 1.15
% 5.02/1.91  Index Insertion      : 0.00
% 5.02/1.91  Index Deletion       : 0.00
% 5.02/1.91  Index Matching       : 0.00
% 5.02/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
