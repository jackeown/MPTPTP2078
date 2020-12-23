%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:45 EST 2020

% Result     : Theorem 9.68s
% Output     : CNFRefutation 9.68s
% Verified   : 
% Statistics : Number of formulae       :  117 (2078 expanded)
%              Number of leaves         :   49 ( 669 expanded)
%              Depth                    :   22
%              Number of atoms          :  159 (4322 expanded)
%              Number of equality atoms :   38 ( 878 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k5_subset_1,type,(
    k5_subset_1: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_149,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_130,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,A))
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & A = k4_tarski(C,k1_tarski(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_144,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_70,plain,(
    ! [A_54] : k2_subset_1(A_54) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_92,plain,(
    k4_subset_1('#skF_8','#skF_9',k2_subset_1('#skF_8')) != k2_subset_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_95,plain,(
    k4_subset_1('#skF_8','#skF_9','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_92])).

tff(c_94,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_288,plain,(
    ! [B_103,A_104] :
      ( v1_xboole_0(B_103)
      | ~ m1_subset_1(B_103,A_104)
      | ~ v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_308,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_94,c_288])).

tff(c_315,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_8220,plain,(
    ! [B_32307,A_32308] :
      ( r2_hidden(B_32307,A_32308)
      | ~ m1_subset_1(B_32307,A_32308)
      | v1_xboole_0(A_32308) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [C_44,A_40] :
      ( r1_tarski(C_44,A_40)
      | ~ r2_hidden(C_44,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10038,plain,(
    ! [B_37337,A_37338] :
      ( r1_tarski(B_37337,A_37338)
      | ~ m1_subset_1(B_37337,k1_zfmisc_1(A_37338))
      | v1_xboole_0(k1_zfmisc_1(A_37338)) ) ),
    inference(resolution,[status(thm)],[c_8220,c_38])).

tff(c_10057,plain,
    ( r1_tarski('#skF_9','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_94,c_10038])).

tff(c_10064,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_10057])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10068,plain,(
    k2_xboole_0('#skF_9','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10064,c_6])).

tff(c_72,plain,(
    ! [A_55] : m1_subset_1(k2_subset_1(A_55),k1_zfmisc_1(A_55)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_96,plain,(
    ! [A_55] : m1_subset_1(A_55,k1_zfmisc_1(A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72])).

tff(c_10579,plain,(
    ! [A_38422,B_38423,C_38424] :
      ( k4_subset_1(A_38422,B_38423,C_38424) = k2_xboole_0(B_38423,C_38424)
      | ~ m1_subset_1(C_38424,k1_zfmisc_1(A_38422))
      | ~ m1_subset_1(B_38423,k1_zfmisc_1(A_38422)) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_14228,plain,(
    ! [A_45230,B_45231] :
      ( k4_subset_1(A_45230,B_45231,A_45230) = k2_xboole_0(B_45231,A_45230)
      | ~ m1_subset_1(B_45231,k1_zfmisc_1(A_45230)) ) ),
    inference(resolution,[status(thm)],[c_96,c_10579])).

tff(c_14258,plain,(
    k4_subset_1('#skF_8','#skF_9','#skF_8') = k2_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_14228])).

tff(c_14274,plain,(
    k4_subset_1('#skF_8','#skF_9','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10068,c_14258])).

tff(c_14276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_14274])).

tff(c_14277,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_14278,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14282,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14277,c_10])).

tff(c_14372,plain,(
    ! [A_45303] :
      ( A_45303 = '#skF_9'
      | ~ v1_xboole_0(A_45303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14282,c_10])).

tff(c_14382,plain,(
    k1_zfmisc_1('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14278,c_14372])).

tff(c_14404,plain,(
    m1_subset_1('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_14382,c_96])).

tff(c_68,plain,(
    ! [B_53,A_52] :
      ( v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14416,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_14404,c_68])).

tff(c_14419,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14277,c_14416])).

tff(c_14284,plain,(
    ! [A_6] :
      ( A_6 = '#skF_9'
      | ~ v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14282,c_10])).

tff(c_14424,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_14419,c_14284])).

tff(c_84,plain,(
    ! [A_71] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_71)) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_14286,plain,(
    ! [A_71] : m1_subset_1('#skF_9',k1_zfmisc_1(A_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14282,c_84])).

tff(c_14430,plain,(
    ! [A_71] : m1_subset_1('#skF_8',k1_zfmisc_1(A_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14424,c_14286])).

tff(c_40,plain,(
    ! [C_44,A_40] :
      ( r2_hidden(C_44,k1_zfmisc_1(A_40))
      | ~ r1_tarski(C_44,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14401,plain,(
    ! [C_44] :
      ( r2_hidden(C_44,'#skF_9')
      | ~ r1_tarski(C_44,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14382,c_40])).

tff(c_14581,plain,(
    ! [C_44] :
      ( r2_hidden(C_44,'#skF_8')
      | ~ r1_tarski(C_44,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14424,c_14401])).

tff(c_14721,plain,(
    ! [C_45328,A_45329,B_45330] :
      ( r2_hidden(C_45328,A_45329)
      | ~ r2_hidden(C_45328,B_45330)
      | ~ m1_subset_1(B_45330,k1_zfmisc_1(A_45329)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14723,plain,(
    ! [C_44,A_45329] :
      ( r2_hidden(C_44,A_45329)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_45329))
      | ~ r1_tarski(C_44,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14581,c_14721])).

tff(c_14732,plain,(
    ! [C_44,A_45329] :
      ( r2_hidden(C_44,A_45329)
      | ~ r1_tarski(C_44,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14430,c_14723])).

tff(c_56,plain,(
    ! [B_48] : k2_zfmisc_1(k1_xboole_0,B_48) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14288,plain,(
    ! [B_48] : k2_zfmisc_1('#skF_9',B_48) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14282,c_14282,c_56])).

tff(c_14483,plain,(
    ! [B_48] : k2_zfmisc_1('#skF_8',B_48) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14424,c_14424,c_14288])).

tff(c_14780,plain,(
    ! [A_45340,B_45341] :
      ( r2_hidden('#skF_5'(A_45340,B_45341),B_45341)
      | ~ r2_hidden(A_45340,k2_zfmisc_1(B_45341,A_45340)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14813,plain,(
    ! [B_45346] :
      ( r2_hidden('#skF_5'(B_45346,'#skF_8'),'#skF_8')
      | ~ r2_hidden(B_45346,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14483,c_14780])).

tff(c_78,plain,(
    ! [C_64,A_61,B_62] :
      ( r2_hidden(C_64,A_61)
      | ~ r2_hidden(C_64,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14815,plain,(
    ! [B_45346,A_61] :
      ( r2_hidden('#skF_5'(B_45346,'#skF_8'),A_61)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_61))
      | ~ r2_hidden(B_45346,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14813,c_78])).

tff(c_14824,plain,(
    ! [B_45346,A_61] :
      ( r2_hidden('#skF_5'(B_45346,'#skF_8'),A_61)
      | ~ r2_hidden(B_45346,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14430,c_14815])).

tff(c_14851,plain,(
    ! [B_45349,A_45350] :
      ( r2_hidden('#skF_5'(B_45349,'#skF_8'),A_45350)
      | ~ r2_hidden(B_45349,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14430,c_14815])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14879,plain,(
    ! [A_45353,B_45354] :
      ( A_45353 = '#skF_5'(B_45354,'#skF_8')
      | ~ r2_hidden(B_45354,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14851,c_12])).

tff(c_15547,plain,(
    ! [B_45400] :
      ( '#skF_5'('#skF_5'(B_45400,'#skF_8'),'#skF_8') = '#skF_9'
      | ~ r2_hidden(B_45400,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14824,c_14879])).

tff(c_14892,plain,(
    ! [A_45353,B_45346] :
      ( A_45353 = '#skF_5'('#skF_5'(B_45346,'#skF_8'),'#skF_8')
      | ~ r2_hidden(B_45346,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14824,c_14879])).

tff(c_15550,plain,(
    ! [A_45353,B_45400] :
      ( A_45353 = '#skF_9'
      | ~ r2_hidden(B_45400,'#skF_8')
      | ~ r2_hidden(B_45400,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15547,c_14892])).

tff(c_17201,plain,(
    ! [A_45353,B_45400] :
      ( A_45353 = '#skF_8'
      | ~ r2_hidden(B_45400,'#skF_8')
      | ~ r2_hidden(B_45400,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14424,c_15550])).

tff(c_17245,plain,(
    ! [B_51096] :
      ( ~ r2_hidden(B_51096,'#skF_8')
      | ~ r2_hidden(B_51096,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_17201])).

tff(c_17267,plain,(
    ! [C_51164] :
      ( ~ r2_hidden(C_51164,'#skF_8')
      | ~ r1_tarski(C_51164,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14732,c_17245])).

tff(c_17291,plain,(
    ! [C_44] : ~ r1_tarski(C_44,'#skF_8') ),
    inference(resolution,[status(thm)],[c_14732,c_17267])).

tff(c_19399,plain,(
    ! [A_51478,B_51479,C_51480] :
      ( r2_hidden('#skF_7'(A_51478,B_51479,C_51480),B_51479)
      | r1_tarski(B_51479,C_51480)
      | ~ m1_subset_1(C_51480,k1_zfmisc_1(A_51478))
      | ~ m1_subset_1(B_51479,k1_zfmisc_1(A_51478)) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_86,plain,(
    ! [A_72,B_73,C_77] :
      ( ~ r2_hidden('#skF_7'(A_72,B_73,C_77),C_77)
      | r1_tarski(B_73,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_19429,plain,(
    ! [B_51481,A_51482] :
      ( r1_tarski(B_51481,B_51481)
      | ~ m1_subset_1(B_51481,k1_zfmisc_1(A_51482)) ) ),
    inference(resolution,[status(thm)],[c_19399,c_86])).

tff(c_19438,plain,(
    r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_14430,c_19429])).

tff(c_19454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17291,c_19438])).

tff(c_19456,plain,(
    ! [A_51483] : A_51483 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_17201])).

tff(c_14437,plain,(
    k4_subset_1('#skF_8','#skF_8','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14424,c_95])).

tff(c_19609,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_19456,c_14437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.68/3.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.37  
% 9.68/3.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 9.68/3.38  
% 9.68/3.38  %Foreground sorts:
% 9.68/3.38  
% 9.68/3.38  
% 9.68/3.38  %Background operators:
% 9.68/3.38  
% 9.68/3.38  
% 9.68/3.38  %Foreground operators:
% 9.68/3.38  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 9.68/3.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.68/3.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.68/3.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.68/3.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.68/3.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.68/3.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.68/3.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.68/3.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.68/3.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.68/3.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.68/3.38  tff(k5_subset_1, type, k5_subset_1: ($i * $i * $i) > $i).
% 9.68/3.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.68/3.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.68/3.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.68/3.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.68/3.38  tff('#skF_9', type, '#skF_9': $i).
% 9.68/3.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.68/3.38  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.68/3.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.68/3.38  tff('#skF_8', type, '#skF_8': $i).
% 9.68/3.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.68/3.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.68/3.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.68/3.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.68/3.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.68/3.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.68/3.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.68/3.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.68/3.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.68/3.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.68/3.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.68/3.38  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.68/3.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.68/3.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.68/3.38  
% 9.68/3.39  tff(f_98, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.68/3.39  tff(f_149, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 9.68/3.39  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.68/3.39  tff(f_66, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.68/3.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.68/3.39  tff(f_100, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.68/3.39  tff(f_122, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.68/3.39  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 9.68/3.39  tff(f_130, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.68/3.39  tff(f_116, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.68/3.39  tff(f_74, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.68/3.39  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, k2_zfmisc_1(B, A)) & (![C]: ~(r2_hidden(C, B) & (A = k4_tarski(C, k1_tarski(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_zfmisc_1)).
% 9.68/3.39  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.68/3.39  tff(f_144, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 9.68/3.39  tff(c_70, plain, (![A_54]: (k2_subset_1(A_54)=A_54)), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.68/3.39  tff(c_92, plain, (k4_subset_1('#skF_8', '#skF_9', k2_subset_1('#skF_8'))!=k2_subset_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.68/3.39  tff(c_95, plain, (k4_subset_1('#skF_8', '#skF_9', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_92])).
% 9.68/3.39  tff(c_94, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.68/3.39  tff(c_288, plain, (![B_103, A_104]: (v1_xboole_0(B_103) | ~m1_subset_1(B_103, A_104) | ~v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.68/3.39  tff(c_308, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_94, c_288])).
% 9.68/3.39  tff(c_315, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_308])).
% 9.68/3.39  tff(c_8220, plain, (![B_32307, A_32308]: (r2_hidden(B_32307, A_32308) | ~m1_subset_1(B_32307, A_32308) | v1_xboole_0(A_32308))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.68/3.39  tff(c_38, plain, (![C_44, A_40]: (r1_tarski(C_44, A_40) | ~r2_hidden(C_44, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.68/3.39  tff(c_10038, plain, (![B_37337, A_37338]: (r1_tarski(B_37337, A_37338) | ~m1_subset_1(B_37337, k1_zfmisc_1(A_37338)) | v1_xboole_0(k1_zfmisc_1(A_37338)))), inference(resolution, [status(thm)], [c_8220, c_38])).
% 9.68/3.39  tff(c_10057, plain, (r1_tarski('#skF_9', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_94, c_10038])).
% 9.68/3.39  tff(c_10064, plain, (r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_315, c_10057])).
% 9.68/3.39  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.68/3.39  tff(c_10068, plain, (k2_xboole_0('#skF_9', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_10064, c_6])).
% 9.68/3.39  tff(c_72, plain, (![A_55]: (m1_subset_1(k2_subset_1(A_55), k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.68/3.39  tff(c_96, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72])).
% 9.68/3.39  tff(c_10579, plain, (![A_38422, B_38423, C_38424]: (k4_subset_1(A_38422, B_38423, C_38424)=k2_xboole_0(B_38423, C_38424) | ~m1_subset_1(C_38424, k1_zfmisc_1(A_38422)) | ~m1_subset_1(B_38423, k1_zfmisc_1(A_38422)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.68/3.39  tff(c_14228, plain, (![A_45230, B_45231]: (k4_subset_1(A_45230, B_45231, A_45230)=k2_xboole_0(B_45231, A_45230) | ~m1_subset_1(B_45231, k1_zfmisc_1(A_45230)))), inference(resolution, [status(thm)], [c_96, c_10579])).
% 9.68/3.39  tff(c_14258, plain, (k4_subset_1('#skF_8', '#skF_9', '#skF_8')=k2_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_94, c_14228])).
% 9.68/3.39  tff(c_14274, plain, (k4_subset_1('#skF_8', '#skF_9', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10068, c_14258])).
% 9.68/3.39  tff(c_14276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_14274])).
% 9.68/3.39  tff(c_14277, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_308])).
% 9.68/3.39  tff(c_14278, plain, (v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitRight, [status(thm)], [c_308])).
% 9.68/3.39  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.68/3.39  tff(c_14282, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_14277, c_10])).
% 9.68/3.39  tff(c_14372, plain, (![A_45303]: (A_45303='#skF_9' | ~v1_xboole_0(A_45303))), inference(demodulation, [status(thm), theory('equality')], [c_14282, c_10])).
% 9.68/3.39  tff(c_14382, plain, (k1_zfmisc_1('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_14278, c_14372])).
% 9.68/3.39  tff(c_14404, plain, (m1_subset_1('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_14382, c_96])).
% 9.68/3.39  tff(c_68, plain, (![B_53, A_52]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.68/3.39  tff(c_14416, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_14404, c_68])).
% 9.68/3.39  tff(c_14419, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14277, c_14416])).
% 9.68/3.39  tff(c_14284, plain, (![A_6]: (A_6='#skF_9' | ~v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_14282, c_10])).
% 9.68/3.39  tff(c_14424, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_14419, c_14284])).
% 9.68/3.39  tff(c_84, plain, (![A_71]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.68/3.39  tff(c_14286, plain, (![A_71]: (m1_subset_1('#skF_9', k1_zfmisc_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_14282, c_84])).
% 9.68/3.39  tff(c_14430, plain, (![A_71]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_14424, c_14286])).
% 9.68/3.39  tff(c_40, plain, (![C_44, A_40]: (r2_hidden(C_44, k1_zfmisc_1(A_40)) | ~r1_tarski(C_44, A_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.68/3.39  tff(c_14401, plain, (![C_44]: (r2_hidden(C_44, '#skF_9') | ~r1_tarski(C_44, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14382, c_40])).
% 9.68/3.39  tff(c_14581, plain, (![C_44]: (r2_hidden(C_44, '#skF_8') | ~r1_tarski(C_44, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14424, c_14401])).
% 9.68/3.39  tff(c_14721, plain, (![C_45328, A_45329, B_45330]: (r2_hidden(C_45328, A_45329) | ~r2_hidden(C_45328, B_45330) | ~m1_subset_1(B_45330, k1_zfmisc_1(A_45329)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.68/3.39  tff(c_14723, plain, (![C_44, A_45329]: (r2_hidden(C_44, A_45329) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_45329)) | ~r1_tarski(C_44, '#skF_8'))), inference(resolution, [status(thm)], [c_14581, c_14721])).
% 9.68/3.39  tff(c_14732, plain, (![C_44, A_45329]: (r2_hidden(C_44, A_45329) | ~r1_tarski(C_44, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14430, c_14723])).
% 9.68/3.39  tff(c_56, plain, (![B_48]: (k2_zfmisc_1(k1_xboole_0, B_48)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.68/3.39  tff(c_14288, plain, (![B_48]: (k2_zfmisc_1('#skF_9', B_48)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14282, c_14282, c_56])).
% 9.68/3.39  tff(c_14483, plain, (![B_48]: (k2_zfmisc_1('#skF_8', B_48)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14424, c_14424, c_14288])).
% 9.68/3.39  tff(c_14780, plain, (![A_45340, B_45341]: (r2_hidden('#skF_5'(A_45340, B_45341), B_45341) | ~r2_hidden(A_45340, k2_zfmisc_1(B_45341, A_45340)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.68/3.39  tff(c_14813, plain, (![B_45346]: (r2_hidden('#skF_5'(B_45346, '#skF_8'), '#skF_8') | ~r2_hidden(B_45346, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14483, c_14780])).
% 9.68/3.39  tff(c_78, plain, (![C_64, A_61, B_62]: (r2_hidden(C_64, A_61) | ~r2_hidden(C_64, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.68/3.39  tff(c_14815, plain, (![B_45346, A_61]: (r2_hidden('#skF_5'(B_45346, '#skF_8'), A_61) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_61)) | ~r2_hidden(B_45346, '#skF_8'))), inference(resolution, [status(thm)], [c_14813, c_78])).
% 9.68/3.39  tff(c_14824, plain, (![B_45346, A_61]: (r2_hidden('#skF_5'(B_45346, '#skF_8'), A_61) | ~r2_hidden(B_45346, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14430, c_14815])).
% 9.68/3.39  tff(c_14851, plain, (![B_45349, A_45350]: (r2_hidden('#skF_5'(B_45349, '#skF_8'), A_45350) | ~r2_hidden(B_45349, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14430, c_14815])).
% 9.68/3.39  tff(c_12, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.68/3.39  tff(c_14879, plain, (![A_45353, B_45354]: (A_45353='#skF_5'(B_45354, '#skF_8') | ~r2_hidden(B_45354, '#skF_8'))), inference(resolution, [status(thm)], [c_14851, c_12])).
% 9.68/3.39  tff(c_15547, plain, (![B_45400]: ('#skF_5'('#skF_5'(B_45400, '#skF_8'), '#skF_8')='#skF_9' | ~r2_hidden(B_45400, '#skF_8'))), inference(resolution, [status(thm)], [c_14824, c_14879])).
% 9.68/3.39  tff(c_14892, plain, (![A_45353, B_45346]: (A_45353='#skF_5'('#skF_5'(B_45346, '#skF_8'), '#skF_8') | ~r2_hidden(B_45346, '#skF_8'))), inference(resolution, [status(thm)], [c_14824, c_14879])).
% 9.68/3.39  tff(c_15550, plain, (![A_45353, B_45400]: (A_45353='#skF_9' | ~r2_hidden(B_45400, '#skF_8') | ~r2_hidden(B_45400, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_15547, c_14892])).
% 9.68/3.39  tff(c_17201, plain, (![A_45353, B_45400]: (A_45353='#skF_8' | ~r2_hidden(B_45400, '#skF_8') | ~r2_hidden(B_45400, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14424, c_15550])).
% 9.68/3.39  tff(c_17245, plain, (![B_51096]: (~r2_hidden(B_51096, '#skF_8') | ~r2_hidden(B_51096, '#skF_8'))), inference(splitLeft, [status(thm)], [c_17201])).
% 9.68/3.39  tff(c_17267, plain, (![C_51164]: (~r2_hidden(C_51164, '#skF_8') | ~r1_tarski(C_51164, '#skF_8'))), inference(resolution, [status(thm)], [c_14732, c_17245])).
% 9.68/3.39  tff(c_17291, plain, (![C_44]: (~r1_tarski(C_44, '#skF_8'))), inference(resolution, [status(thm)], [c_14732, c_17267])).
% 9.68/3.39  tff(c_19399, plain, (![A_51478, B_51479, C_51480]: (r2_hidden('#skF_7'(A_51478, B_51479, C_51480), B_51479) | r1_tarski(B_51479, C_51480) | ~m1_subset_1(C_51480, k1_zfmisc_1(A_51478)) | ~m1_subset_1(B_51479, k1_zfmisc_1(A_51478)))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.39  tff(c_86, plain, (![A_72, B_73, C_77]: (~r2_hidden('#skF_7'(A_72, B_73, C_77), C_77) | r1_tarski(B_73, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.39  tff(c_19429, plain, (![B_51481, A_51482]: (r1_tarski(B_51481, B_51481) | ~m1_subset_1(B_51481, k1_zfmisc_1(A_51482)))), inference(resolution, [status(thm)], [c_19399, c_86])).
% 9.68/3.39  tff(c_19438, plain, (r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_14430, c_19429])).
% 9.68/3.39  tff(c_19454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17291, c_19438])).
% 9.68/3.39  tff(c_19456, plain, (![A_51483]: (A_51483='#skF_8')), inference(splitRight, [status(thm)], [c_17201])).
% 9.68/3.39  tff(c_14437, plain, (k4_subset_1('#skF_8', '#skF_8', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_14424, c_95])).
% 9.68/3.39  tff(c_19609, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_19456, c_14437])).
% 9.68/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.39  
% 9.68/3.39  Inference rules
% 9.68/3.39  ----------------------
% 9.68/3.39  #Ref     : 0
% 9.68/3.39  #Sup     : 4541
% 9.68/3.39  #Fact    : 6
% 9.68/3.39  #Define  : 0
% 9.68/3.39  #Split   : 10
% 9.68/3.39  #Chain   : 0
% 9.68/3.39  #Close   : 0
% 9.68/3.39  
% 9.68/3.39  Ordering : KBO
% 9.68/3.39  
% 9.68/3.39  Simplification rules
% 9.68/3.39  ----------------------
% 9.68/3.39  #Subsume      : 1490
% 9.68/3.39  #Demod        : 1019
% 9.68/3.39  #Tautology    : 1194
% 9.68/3.39  #SimpNegUnit  : 78
% 9.68/3.39  #BackRed      : 38
% 9.68/3.39  
% 9.68/3.39  #Partial instantiations: 18199
% 9.68/3.39  #Strategies tried      : 1
% 9.68/3.39  
% 9.68/3.39  Timing (in seconds)
% 9.68/3.39  ----------------------
% 9.68/3.40  Preprocessing        : 0.36
% 9.68/3.40  Parsing              : 0.18
% 9.68/3.40  CNF conversion       : 0.03
% 9.68/3.40  Main loop            : 2.23
% 9.68/3.40  Inferencing          : 0.89
% 9.68/3.40  Reduction            : 0.69
% 9.68/3.40  Demodulation         : 0.49
% 10.00/3.40  BG Simplification    : 0.07
% 10.00/3.40  Subsumption          : 0.43
% 10.00/3.40  Abstraction          : 0.10
% 10.00/3.40  MUC search           : 0.00
% 10.00/3.40  Cooper               : 0.00
% 10.00/3.40  Total                : 2.63
% 10.00/3.40  Index Insertion      : 0.00
% 10.00/3.40  Index Deletion       : 0.00
% 10.00/3.40  Index Matching       : 0.00
% 10.00/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
