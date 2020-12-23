%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:12 EST 2020

% Result     : Theorem 46.99s
% Output     : CNFRefutation 47.15s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 123 expanded)
%              Number of leaves         :   38 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 176 expanded)
%              Number of equality atoms :   29 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_66,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [A_51] : k2_relat_1(k6_relat_1(A_51)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,(
    ! [A_102,B_103] :
      ( k8_relat_1(A_102,B_103) = B_103
      | ~ r1_tarski(k2_relat_1(B_103),A_102)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_360,plain,(
    ! [B_103] :
      ( k8_relat_1(k2_relat_1(B_103),B_103) = B_103
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_337])).

tff(c_585,plain,(
    ! [B_120,A_121] :
      ( k3_xboole_0(k2_relat_1(B_120),A_121) = k2_relat_1(k8_relat_1(A_121,B_120))
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_608,plain,(
    ! [A_121,A_51] :
      ( k2_relat_1(k8_relat_1(A_121,k6_relat_1(A_51))) = k3_xboole_0(A_51,A_121)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_585])).

tff(c_615,plain,(
    ! [A_122,A_123] : k2_relat_1(k8_relat_1(A_122,k6_relat_1(A_123))) = k3_xboole_0(A_123,A_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_608])).

tff(c_646,plain,(
    ! [A_123] :
      ( k3_xboole_0(A_123,k2_relat_1(k6_relat_1(A_123))) = k2_relat_1(k6_relat_1(A_123))
      | ~ v1_relat_1(k6_relat_1(A_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_615])).

tff(c_662,plain,(
    ! [A_123] : k3_xboole_0(A_123,A_123) = A_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_44,c_646])).

tff(c_612,plain,(
    ! [A_121,A_51] : k2_relat_1(k8_relat_1(A_121,k6_relat_1(A_51))) = k3_xboole_0(A_51,A_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_608])).

tff(c_282,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_94,B_95)),k2_relat_1(B_95))
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_292,plain,(
    ! [A_94,A_51] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_94,k6_relat_1(A_51))),A_51)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_282])).

tff(c_297,plain,(
    ! [A_94,A_51] : r1_tarski(k2_relat_1(k8_relat_1(A_94,k6_relat_1(A_51))),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_292])).

tff(c_614,plain,(
    ! [A_51,A_94] : r1_tarski(k3_xboole_0(A_51,A_94),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_297])).

tff(c_310,plain,(
    ! [B_100,A_101] :
      ( k5_relat_1(B_100,k6_relat_1(A_101)) = k8_relat_1(A_101,B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ! [B_53,A_52] :
      ( r1_tarski(k5_relat_1(B_53,k6_relat_1(A_52)),B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_557,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k8_relat_1(A_118,B_119),B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_48])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7522,plain,(
    ! [A_301,B_302,A_303] :
      ( r1_tarski(A_301,B_302)
      | ~ r1_tarski(A_301,k8_relat_1(A_303,B_302))
      | ~ v1_relat_1(B_302) ) ),
    inference(resolution,[status(thm)],[c_557,c_8])).

tff(c_10240,plain,(
    ! [A_355,B_356,A_357] :
      ( r1_tarski(k3_xboole_0(k8_relat_1(A_355,B_356),A_357),B_356)
      | ~ v1_relat_1(B_356) ) ),
    inference(resolution,[status(thm)],[c_614,c_7522])).

tff(c_28,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_215,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_219,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(A_37)
      | ~ v1_relat_1(B_38)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_10374,plain,(
    ! [A_358,B_359,A_360] :
      ( v1_relat_1(k3_xboole_0(k8_relat_1(A_358,B_359),A_360))
      | ~ v1_relat_1(B_359) ) ),
    inference(resolution,[status(thm)],[c_10240,c_219])).

tff(c_10402,plain,(
    ! [A_358,B_359] :
      ( v1_relat_1(k8_relat_1(A_358,B_359))
      | ~ v1_relat_1(B_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_10374])).

tff(c_36,plain,(
    ! [B_46,A_45] :
      ( k3_xboole_0(k2_relat_1(B_46),A_45) = k2_relat_1(k8_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    ! [A_64,B_65] : k1_setfam_1(k2_tarski(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,(
    ! [B_68,A_69] : k1_setfam_1(k2_tarski(B_68,A_69)) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_119])).

tff(c_24,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_145,plain,(
    ! [B_68,A_69] : k3_xboole_0(B_68,A_69) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_24])).

tff(c_692,plain,(
    ! [A_126,A_127] : r1_tarski(k3_xboole_0(A_126,A_127),A_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_297])).

tff(c_720,plain,(
    ! [B_128,A_129] : r1_tarski(k3_xboole_0(B_128,A_129),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_692])).

tff(c_2664,plain,(
    ! [A_209,B_210] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_209,B_210)),A_209)
      | ~ v1_relat_1(B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_720])).

tff(c_52,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_238,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(A_82,C_83)
      | ~ r1_tarski(B_84,C_83)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_250,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_2')
      | ~ r1_tarski(A_82,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_238])).

tff(c_357,plain,(
    ! [B_103] :
      ( k8_relat_1('#skF_2',B_103) = B_103
      | ~ v1_relat_1(B_103)
      | ~ r1_tarski(k2_relat_1(B_103),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_250,c_337])).

tff(c_23087,plain,(
    ! [B_614] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_614)) = k8_relat_1('#skF_1',B_614)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_614))
      | ~ v1_relat_1(B_614) ) ),
    inference(resolution,[status(thm)],[c_2664,c_357])).

tff(c_152002,plain,(
    ! [B_1842] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_1842)) = k8_relat_1('#skF_1',B_1842)
      | ~ v1_relat_1(B_1842) ) ),
    inference(resolution,[status(thm)],[c_10402,c_23087])).

tff(c_50,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_152354,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152002,c_50])).

tff(c_152450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_152354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 46.99/37.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 46.99/37.15  
% 46.99/37.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 46.99/37.15  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 46.99/37.15  
% 46.99/37.15  %Foreground sorts:
% 46.99/37.15  
% 46.99/37.15  
% 46.99/37.15  %Background operators:
% 46.99/37.15  
% 46.99/37.15  
% 46.99/37.15  %Foreground operators:
% 46.99/37.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 46.99/37.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 46.99/37.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 46.99/37.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 46.99/37.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 46.99/37.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 46.99/37.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 46.99/37.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 46.99/37.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 46.99/37.15  tff('#skF_2', type, '#skF_2': $i).
% 46.99/37.15  tff('#skF_3', type, '#skF_3': $i).
% 46.99/37.15  tff('#skF_1', type, '#skF_1': $i).
% 46.99/37.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 46.99/37.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 46.99/37.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 46.99/37.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 46.99/37.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 46.99/37.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 46.99/37.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 46.99/37.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 46.99/37.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 46.99/37.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 46.99/37.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 46.99/37.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 46.99/37.15  
% 47.15/37.18  tff(f_101, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 47.15/37.18  tff(f_66, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 47.15/37.18  tff(f_88, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 47.15/37.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 47.15/37.18  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 47.15/37.18  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 47.15/37.18  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_relat_1)).
% 47.15/37.18  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 47.15/37.18  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 47.15/37.18  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 47.15/37.18  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 47.15/37.18  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 47.15/37.18  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 47.15/37.18  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 47.15/37.18  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 47.15/37.18  tff(c_32, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 47.15/37.18  tff(c_44, plain, (![A_51]: (k2_relat_1(k6_relat_1(A_51))=A_51)), inference(cnfTransformation, [status(thm)], [f_88])).
% 47.15/37.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.15/37.18  tff(c_337, plain, (![A_102, B_103]: (k8_relat_1(A_102, B_103)=B_103 | ~r1_tarski(k2_relat_1(B_103), A_102) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_84])).
% 47.15/37.18  tff(c_360, plain, (![B_103]: (k8_relat_1(k2_relat_1(B_103), B_103)=B_103 | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_6, c_337])).
% 47.15/37.18  tff(c_585, plain, (![B_120, A_121]: (k3_xboole_0(k2_relat_1(B_120), A_121)=k2_relat_1(k8_relat_1(A_121, B_120)) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_74])).
% 47.15/37.18  tff(c_608, plain, (![A_121, A_51]: (k2_relat_1(k8_relat_1(A_121, k6_relat_1(A_51)))=k3_xboole_0(A_51, A_121) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_585])).
% 47.15/37.18  tff(c_615, plain, (![A_122, A_123]: (k2_relat_1(k8_relat_1(A_122, k6_relat_1(A_123)))=k3_xboole_0(A_123, A_122))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_608])).
% 47.15/37.18  tff(c_646, plain, (![A_123]: (k3_xboole_0(A_123, k2_relat_1(k6_relat_1(A_123)))=k2_relat_1(k6_relat_1(A_123)) | ~v1_relat_1(k6_relat_1(A_123)))), inference(superposition, [status(thm), theory('equality')], [c_360, c_615])).
% 47.15/37.18  tff(c_662, plain, (![A_123]: (k3_xboole_0(A_123, A_123)=A_123)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_44, c_646])).
% 47.15/37.18  tff(c_612, plain, (![A_121, A_51]: (k2_relat_1(k8_relat_1(A_121, k6_relat_1(A_51)))=k3_xboole_0(A_51, A_121))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_608])).
% 47.15/37.18  tff(c_282, plain, (![A_94, B_95]: (r1_tarski(k2_relat_1(k8_relat_1(A_94, B_95)), k2_relat_1(B_95)) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 47.15/37.18  tff(c_292, plain, (![A_94, A_51]: (r1_tarski(k2_relat_1(k8_relat_1(A_94, k6_relat_1(A_51))), A_51) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_282])).
% 47.15/37.18  tff(c_297, plain, (![A_94, A_51]: (r1_tarski(k2_relat_1(k8_relat_1(A_94, k6_relat_1(A_51))), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_292])).
% 47.15/37.18  tff(c_614, plain, (![A_51, A_94]: (r1_tarski(k3_xboole_0(A_51, A_94), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_297])).
% 47.15/37.18  tff(c_310, plain, (![B_100, A_101]: (k5_relat_1(B_100, k6_relat_1(A_101))=k8_relat_1(A_101, B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 47.15/37.18  tff(c_48, plain, (![B_53, A_52]: (r1_tarski(k5_relat_1(B_53, k6_relat_1(A_52)), B_53) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_94])).
% 47.15/37.18  tff(c_557, plain, (![A_118, B_119]: (r1_tarski(k8_relat_1(A_118, B_119), B_119) | ~v1_relat_1(B_119) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_310, c_48])).
% 47.15/37.18  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 47.15/37.18  tff(c_7522, plain, (![A_301, B_302, A_303]: (r1_tarski(A_301, B_302) | ~r1_tarski(A_301, k8_relat_1(A_303, B_302)) | ~v1_relat_1(B_302))), inference(resolution, [status(thm)], [c_557, c_8])).
% 47.15/37.18  tff(c_10240, plain, (![A_355, B_356, A_357]: (r1_tarski(k3_xboole_0(k8_relat_1(A_355, B_356), A_357), B_356) | ~v1_relat_1(B_356))), inference(resolution, [status(thm)], [c_614, c_7522])).
% 47.15/37.18  tff(c_28, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 47.15/37.18  tff(c_215, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_64])).
% 47.15/37.18  tff(c_219, plain, (![A_37, B_38]: (v1_relat_1(A_37) | ~v1_relat_1(B_38) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_28, c_215])).
% 47.15/37.18  tff(c_10374, plain, (![A_358, B_359, A_360]: (v1_relat_1(k3_xboole_0(k8_relat_1(A_358, B_359), A_360)) | ~v1_relat_1(B_359))), inference(resolution, [status(thm)], [c_10240, c_219])).
% 47.15/37.18  tff(c_10402, plain, (![A_358, B_359]: (v1_relat_1(k8_relat_1(A_358, B_359)) | ~v1_relat_1(B_359))), inference(superposition, [status(thm), theory('equality')], [c_662, c_10374])).
% 47.15/37.18  tff(c_36, plain, (![B_46, A_45]: (k3_xboole_0(k2_relat_1(B_46), A_45)=k2_relat_1(k8_relat_1(A_45, B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 47.15/37.18  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 47.15/37.18  tff(c_119, plain, (![A_64, B_65]: (k1_setfam_1(k2_tarski(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 47.15/37.18  tff(c_139, plain, (![B_68, A_69]: (k1_setfam_1(k2_tarski(B_68, A_69))=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_10, c_119])).
% 47.15/37.18  tff(c_24, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 47.15/37.18  tff(c_145, plain, (![B_68, A_69]: (k3_xboole_0(B_68, A_69)=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_139, c_24])).
% 47.15/37.18  tff(c_692, plain, (![A_126, A_127]: (r1_tarski(k3_xboole_0(A_126, A_127), A_126))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_297])).
% 47.15/37.18  tff(c_720, plain, (![B_128, A_129]: (r1_tarski(k3_xboole_0(B_128, A_129), A_129))), inference(superposition, [status(thm), theory('equality')], [c_145, c_692])).
% 47.15/37.18  tff(c_2664, plain, (![A_209, B_210]: (r1_tarski(k2_relat_1(k8_relat_1(A_209, B_210)), A_209) | ~v1_relat_1(B_210))), inference(superposition, [status(thm), theory('equality')], [c_36, c_720])).
% 47.15/37.18  tff(c_52, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 47.15/37.18  tff(c_238, plain, (![A_82, C_83, B_84]: (r1_tarski(A_82, C_83) | ~r1_tarski(B_84, C_83) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 47.15/37.18  tff(c_250, plain, (![A_82]: (r1_tarski(A_82, '#skF_2') | ~r1_tarski(A_82, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_238])).
% 47.15/37.18  tff(c_357, plain, (![B_103]: (k8_relat_1('#skF_2', B_103)=B_103 | ~v1_relat_1(B_103) | ~r1_tarski(k2_relat_1(B_103), '#skF_1'))), inference(resolution, [status(thm)], [c_250, c_337])).
% 47.15/37.18  tff(c_23087, plain, (![B_614]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_614))=k8_relat_1('#skF_1', B_614) | ~v1_relat_1(k8_relat_1('#skF_1', B_614)) | ~v1_relat_1(B_614))), inference(resolution, [status(thm)], [c_2664, c_357])).
% 47.15/37.18  tff(c_152002, plain, (![B_1842]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_1842))=k8_relat_1('#skF_1', B_1842) | ~v1_relat_1(B_1842))), inference(resolution, [status(thm)], [c_10402, c_23087])).
% 47.15/37.18  tff(c_50, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 47.15/37.18  tff(c_152354, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152002, c_50])).
% 47.15/37.18  tff(c_152450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_152354])).
% 47.15/37.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.15/37.18  
% 47.15/37.18  Inference rules
% 47.15/37.18  ----------------------
% 47.15/37.18  #Ref     : 0
% 47.15/37.18  #Sup     : 37766
% 47.15/37.18  #Fact    : 0
% 47.15/37.18  #Define  : 0
% 47.15/37.18  #Split   : 9
% 47.15/37.18  #Chain   : 0
% 47.15/37.18  #Close   : 0
% 47.15/37.18  
% 47.15/37.18  Ordering : KBO
% 47.15/37.18  
% 47.15/37.18  Simplification rules
% 47.15/37.18  ----------------------
% 47.15/37.18  #Subsume      : 13495
% 47.15/37.18  #Demod        : 28454
% 47.15/37.18  #Tautology    : 11064
% 47.15/37.18  #SimpNegUnit  : 106
% 47.15/37.18  #BackRed      : 13
% 47.15/37.18  
% 47.15/37.18  #Partial instantiations: 0
% 47.15/37.18  #Strategies tried      : 1
% 47.15/37.18  
% 47.15/37.18  Timing (in seconds)
% 47.15/37.18  ----------------------
% 47.15/37.18  Preprocessing        : 0.33
% 47.15/37.18  Parsing              : 0.18
% 47.15/37.18  CNF conversion       : 0.02
% 47.15/37.18  Main loop            : 36.04
% 47.15/37.18  Inferencing          : 3.13
% 47.15/37.18  Reduction            : 19.53
% 47.15/37.18  Demodulation         : 17.28
% 47.15/37.18  BG Simplification    : 0.32
% 47.15/37.19  Subsumption          : 11.88
% 47.15/37.19  Abstraction          : 0.58
% 47.15/37.19  MUC search           : 0.00
% 47.15/37.19  Cooper               : 0.00
% 47.15/37.19  Total                : 36.42
% 47.15/37.19  Index Insertion      : 0.00
% 47.15/37.19  Index Deletion       : 0.00
% 47.15/37.19  Index Matching       : 0.00
% 47.15/37.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
