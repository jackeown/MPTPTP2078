%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 180 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 343 expanded)
%              Number of equality atoms :   36 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_28,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) != k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_89,plain,(
    ! [A_34,C_35,B_36] :
      ( m1_subset_1(A_34,C_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_92,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_89])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    ! [A_26,B_27] : ~ r2_hidden(A_26,k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k7_setfam_1(A_11,B_12),k1_zfmisc_1(k1_zfmisc_1(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [A_40,B_41] :
      ( k7_setfam_1(A_40,k7_setfam_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_141,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k7_setfam_1(A_46,B_47),k1_zfmisc_1(k1_zfmisc_1(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_19,C_21,B_20] :
      ( m1_subset_1(A_19,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_21))
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_160,plain,(
    ! [A_51,A_52,B_53] :
      ( m1_subset_1(A_51,k1_zfmisc_1(A_52))
      | ~ r2_hidden(A_51,k7_setfam_1(A_52,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(resolution,[status(thm)],[c_141,c_24])).

tff(c_261,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_65,B_66)),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65)))
      | k7_setfam_1(A_65,B_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_160])).

tff(c_280,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_261])).

tff(c_287,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_280])).

tff(c_288,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_287])).

tff(c_289,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_292,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_292])).

tff(c_298,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_1182,plain,(
    ! [A_98] :
      ( m1_subset_1(A_98,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_98,k7_setfam_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_298,c_24])).

tff(c_1194,plain,
    ( m1_subset_1('#skF_1'(k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_2'))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1182])).

tff(c_1195,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_20,plain,(
    ! [A_15,C_18,B_16] :
      ( r2_hidden(k3_subset_1(A_15,C_18),k7_setfam_1(A_15,B_16))
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1206,plain,(
    ! [C_18] :
      ( r2_hidden(k3_subset_1('#skF_2',C_18),k1_xboole_0)
      | ~ r2_hidden(C_18,'#skF_3')
      | ~ m1_subset_1(C_18,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1195,c_20])).

tff(c_1221,plain,(
    ! [C_18] :
      ( r2_hidden(k3_subset_1('#skF_2',C_18),k1_xboole_0)
      | ~ r2_hidden(C_18,'#skF_3')
      | ~ m1_subset_1(C_18,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1206])).

tff(c_1302,plain,(
    ! [C_101] :
      ( ~ r2_hidden(C_101,'#skF_3')
      | ~ m1_subset_1(C_101,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1221])).

tff(c_1326,plain,(
    ! [A_102] : ~ r2_hidden(A_102,'#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_1302])).

tff(c_1330,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_1326])).

tff(c_1334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1330])).

tff(c_1336,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_194,plain,(
    ! [A_56,B_57] :
      ( k6_setfam_1(A_56,k7_setfam_1(A_56,B_57)) = k3_subset_1(A_56,k5_setfam_1(A_56,B_57))
      | k1_xboole_0 = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1546,plain,(
    ! [A_109,B_110] :
      ( k6_setfam_1(A_109,k7_setfam_1(A_109,k7_setfam_1(A_109,B_110))) = k3_subset_1(A_109,k5_setfam_1(A_109,k7_setfam_1(A_109,B_110)))
      | k7_setfam_1(A_109,B_110) = k1_xboole_0
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(resolution,[status(thm)],[c_16,c_194])).

tff(c_1561,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1546])).

tff(c_1570,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_1561])).

tff(c_1571,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1336,c_1570])).

tff(c_130,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k5_setfam_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_subset_1(A_7,k3_subset_1(A_7,B_8)) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,k5_setfam_1(A_44,B_45))) = k5_setfam_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(resolution,[status(thm)],[c_130,c_12])).

tff(c_321,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_298,c_140])).

tff(c_1739,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_321])).

tff(c_1740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:50:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.65  
% 3.87/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.66  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.87/1.66  
% 3.87/1.66  %Foreground sorts:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Background operators:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Foreground operators:
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.87/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.66  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.87/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.87/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.66  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.87/1.66  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.66  
% 3.87/1.67  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 3.87/1.67  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.87/1.67  tff(f_73, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.87/1.67  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.87/1.67  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.87/1.67  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.87/1.67  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.87/1.67  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 3.87/1.67  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 3.87/1.67  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.87/1.67  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.87/1.67  tff(c_28, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.67  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.67  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.67  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.67  tff(c_89, plain, (![A_34, C_35, B_36]: (m1_subset_1(A_34, C_35) | ~m1_subset_1(B_36, k1_zfmisc_1(C_35)) | ~r2_hidden(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.87/1.67  tff(c_92, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_89])).
% 3.87/1.67  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.87/1.67  tff(c_55, plain, (![A_26, B_27]: (~r2_hidden(A_26, k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.87/1.67  tff(c_58, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_55])).
% 3.87/1.67  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k7_setfam_1(A_11, B_12), k1_zfmisc_1(k1_zfmisc_1(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.87/1.67  tff(c_104, plain, (![A_40, B_41]: (k7_setfam_1(A_40, k7_setfam_1(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.87/1.67  tff(c_107, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_104])).
% 3.87/1.67  tff(c_141, plain, (![A_46, B_47]: (m1_subset_1(k7_setfam_1(A_46, B_47), k1_zfmisc_1(k1_zfmisc_1(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.87/1.67  tff(c_24, plain, (![A_19, C_21, B_20]: (m1_subset_1(A_19, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(C_21)) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.87/1.67  tff(c_160, plain, (![A_51, A_52, B_53]: (m1_subset_1(A_51, k1_zfmisc_1(A_52)) | ~r2_hidden(A_51, k7_setfam_1(A_52, B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(resolution, [status(thm)], [c_141, c_24])).
% 3.87/1.67  tff(c_261, plain, (![A_65, B_66]: (m1_subset_1('#skF_1'(k7_setfam_1(A_65, B_66)), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))) | k7_setfam_1(A_65, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_160])).
% 3.87/1.67  tff(c_280, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_107, c_261])).
% 3.87/1.67  tff(c_287, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_280])).
% 3.87/1.67  tff(c_288, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_287])).
% 3.87/1.67  tff(c_289, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_288])).
% 3.87/1.67  tff(c_292, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_289])).
% 3.87/1.67  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_292])).
% 3.87/1.67  tff(c_298, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_288])).
% 3.87/1.67  tff(c_1182, plain, (![A_98]: (m1_subset_1(A_98, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_98, k7_setfam_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_298, c_24])).
% 3.87/1.67  tff(c_1194, plain, (m1_subset_1('#skF_1'(k7_setfam_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_2')) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1182])).
% 3.87/1.67  tff(c_1195, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1194])).
% 3.87/1.67  tff(c_20, plain, (![A_15, C_18, B_16]: (r2_hidden(k3_subset_1(A_15, C_18), k7_setfam_1(A_15, B_16)) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(C_18, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.87/1.67  tff(c_1206, plain, (![C_18]: (r2_hidden(k3_subset_1('#skF_2', C_18), k1_xboole_0) | ~r2_hidden(C_18, '#skF_3') | ~m1_subset_1(C_18, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1195, c_20])).
% 3.87/1.67  tff(c_1221, plain, (![C_18]: (r2_hidden(k3_subset_1('#skF_2', C_18), k1_xboole_0) | ~r2_hidden(C_18, '#skF_3') | ~m1_subset_1(C_18, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1206])).
% 3.87/1.67  tff(c_1302, plain, (![C_101]: (~r2_hidden(C_101, '#skF_3') | ~m1_subset_1(C_101, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1221])).
% 3.87/1.67  tff(c_1326, plain, (![A_102]: (~r2_hidden(A_102, '#skF_3'))), inference(resolution, [status(thm)], [c_92, c_1302])).
% 3.87/1.67  tff(c_1330, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_1326])).
% 3.87/1.67  tff(c_1334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1330])).
% 3.87/1.67  tff(c_1336, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1194])).
% 3.87/1.67  tff(c_194, plain, (![A_56, B_57]: (k6_setfam_1(A_56, k7_setfam_1(A_56, B_57))=k3_subset_1(A_56, k5_setfam_1(A_56, B_57)) | k1_xboole_0=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.87/1.67  tff(c_1546, plain, (![A_109, B_110]: (k6_setfam_1(A_109, k7_setfam_1(A_109, k7_setfam_1(A_109, B_110)))=k3_subset_1(A_109, k5_setfam_1(A_109, k7_setfam_1(A_109, B_110))) | k7_setfam_1(A_109, B_110)=k1_xboole_0 | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(resolution, [status(thm)], [c_16, c_194])).
% 3.87/1.67  tff(c_1561, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1546])).
% 3.87/1.67  tff(c_1570, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_1561])).
% 3.87/1.67  tff(c_1571, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1336, c_1570])).
% 3.87/1.67  tff(c_130, plain, (![A_44, B_45]: (m1_subset_1(k5_setfam_1(A_44, B_45), k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.87/1.67  tff(c_12, plain, (![A_7, B_8]: (k3_subset_1(A_7, k3_subset_1(A_7, B_8))=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.87/1.67  tff(c_140, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, k5_setfam_1(A_44, B_45)))=k5_setfam_1(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(resolution, [status(thm)], [c_130, c_12])).
% 3.87/1.67  tff(c_321, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_298, c_140])).
% 3.87/1.67  tff(c_1739, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_321])).
% 3.87/1.67  tff(c_1740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1739])).
% 3.87/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.67  
% 3.87/1.67  Inference rules
% 3.87/1.67  ----------------------
% 3.87/1.67  #Ref     : 0
% 3.87/1.67  #Sup     : 414
% 3.87/1.67  #Fact    : 0
% 3.87/1.67  #Define  : 0
% 3.87/1.67  #Split   : 19
% 3.87/1.67  #Chain   : 0
% 3.87/1.67  #Close   : 0
% 3.87/1.67  
% 3.87/1.67  Ordering : KBO
% 3.87/1.67  
% 3.87/1.67  Simplification rules
% 3.87/1.67  ----------------------
% 3.87/1.67  #Subsume      : 47
% 3.87/1.67  #Demod        : 205
% 3.87/1.67  #Tautology    : 163
% 3.87/1.67  #SimpNegUnit  : 30
% 3.87/1.67  #BackRed      : 38
% 3.87/1.67  
% 3.87/1.67  #Partial instantiations: 0
% 3.87/1.67  #Strategies tried      : 1
% 3.87/1.67  
% 3.87/1.67  Timing (in seconds)
% 3.87/1.67  ----------------------
% 3.87/1.67  Preprocessing        : 0.31
% 3.87/1.67  Parsing              : 0.17
% 3.87/1.67  CNF conversion       : 0.02
% 3.87/1.67  Main loop            : 0.55
% 3.87/1.67  Inferencing          : 0.19
% 3.87/1.67  Reduction            : 0.17
% 3.87/1.67  Demodulation         : 0.12
% 3.87/1.67  BG Simplification    : 0.03
% 3.87/1.68  Subsumption          : 0.12
% 3.87/1.68  Abstraction          : 0.03
% 3.87/1.68  MUC search           : 0.00
% 3.87/1.68  Cooper               : 0.00
% 3.87/1.68  Total                : 0.90
% 3.87/1.68  Index Insertion      : 0.00
% 3.87/1.68  Index Deletion       : 0.00
% 3.87/1.68  Index Matching       : 0.00
% 3.87/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
