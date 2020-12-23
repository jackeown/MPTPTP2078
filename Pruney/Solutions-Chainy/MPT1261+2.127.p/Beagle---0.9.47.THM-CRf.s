%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:29 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 118 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 240 expanded)
%              Number of equality atoms :   49 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1287,plain,(
    ! [A_103,B_104,C_105] :
      ( k7_subset_1(A_103,B_104,C_105) = k4_xboole_0(B_104,C_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1290,plain,(
    ! [C_105] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_105) = k4_xboole_0('#skF_2',C_105) ),
    inference(resolution,[status(thm)],[c_24,c_1287])).

tff(c_36,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_156,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_220,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_30])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_599,plain,(
    ! [B_68,A_69] :
      ( v4_pre_topc(B_68,A_69)
      | k2_pre_topc(A_69,B_68) != B_68
      | ~ v2_pre_topc(A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_605,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_599])).

tff(c_609,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_605])).

tff(c_610,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_609])).

tff(c_830,plain,(
    ! [A_76,B_77] :
      ( k4_subset_1(u1_struct_0(A_76),B_77,k2_tops_1(A_76,B_77)) = k2_pre_topc(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_834,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_830])).

tff(c_838,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_834])).

tff(c_179,plain,(
    ! [A_41,B_42,C_43] :
      ( k7_subset_1(A_41,B_42,C_43) = k4_xboole_0(B_42,C_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [C_44] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_44) = k4_xboole_0('#skF_2',C_44) ),
    inference(resolution,[status(thm)],[c_24,c_179])).

tff(c_189,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_156])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_33,B_34] : k2_xboole_0(k4_xboole_0(A_33,B_34),k3_xboole_0(A_33,B_34)) = k2_xboole_0(k4_xboole_0(A_33,B_34),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_4])).

tff(c_269,plain,(
    ! [A_47,B_48] : k2_xboole_0(k4_xboole_0(A_47,B_48),k3_xboole_0(A_47,B_48)) = k2_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_275,plain,(
    ! [A_47,B_48] : k2_xboole_0(k3_xboole_0(A_47,B_48),k4_xboole_0(A_47,B_48)) = k2_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_2])).

tff(c_315,plain,(
    ! [A_49,B_50] : k2_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_275])).

tff(c_331,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_315])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_446,plain,(
    ! [A_60,B_61,C_62] :
      ( k4_subset_1(A_60,B_61,C_62) = k2_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1240,plain,(
    ! [A_97,B_98,B_99] :
      ( k4_subset_1(u1_struct_0(A_97),B_98,k2_tops_1(A_97,B_99)) = k2_xboole_0(B_98,k2_tops_1(A_97,B_99))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_18,c_446])).

tff(c_1244,plain,(
    ! [B_99] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_99)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1240])).

tff(c_1249,plain,(
    ! [B_100] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_100)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_100))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1244])).

tff(c_1256,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_1249])).

tff(c_1261,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_331,c_1256])).

tff(c_1263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_1261])).

tff(c_1265,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1291,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_1265])).

tff(c_1264,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1334,plain,(
    ! [A_109,B_110] :
      ( k2_pre_topc(A_109,B_110) = B_110
      | ~ v4_pre_topc(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1337,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1334])).

tff(c_1340,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1264,c_1337])).

tff(c_1717,plain,(
    ! [A_141,B_142] :
      ( k7_subset_1(u1_struct_0(A_141),k2_pre_topc(A_141,B_142),k1_tops_1(A_141,B_142)) = k2_tops_1(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1726,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_1717])).

tff(c_1730,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1290,c_1726])).

tff(c_1732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1291,c_1730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.61  
% 3.72/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.62  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.72/1.62  
% 3.72/1.62  %Foreground sorts:
% 3.72/1.62  
% 3.72/1.62  
% 3.72/1.62  %Background operators:
% 3.72/1.62  
% 3.72/1.62  
% 3.72/1.62  %Foreground operators:
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.72/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.72/1.62  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.72/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.72/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.62  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.72/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.62  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.72/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.72/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.72/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.62  
% 3.72/1.63  tff(f_90, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.72/1.63  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.72/1.63  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.72/1.63  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.72/1.63  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.72/1.63  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.72/1.63  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.72/1.63  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.72/1.63  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.72/1.63  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.72/1.63  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.72/1.63  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.63  tff(c_1287, plain, (![A_103, B_104, C_105]: (k7_subset_1(A_103, B_104, C_105)=k4_xboole_0(B_104, C_105) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.72/1.63  tff(c_1290, plain, (![C_105]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_105)=k4_xboole_0('#skF_2', C_105))), inference(resolution, [status(thm)], [c_24, c_1287])).
% 3.72/1.63  tff(c_36, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.63  tff(c_156, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 3.72/1.63  tff(c_30, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.63  tff(c_220, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_30])).
% 3.72/1.63  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.63  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.63  tff(c_599, plain, (![B_68, A_69]: (v4_pre_topc(B_68, A_69) | k2_pre_topc(A_69, B_68)!=B_68 | ~v2_pre_topc(A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.63  tff(c_605, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_599])).
% 3.72/1.63  tff(c_609, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_605])).
% 3.72/1.63  tff(c_610, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_220, c_609])).
% 3.72/1.63  tff(c_830, plain, (![A_76, B_77]: (k4_subset_1(u1_struct_0(A_76), B_77, k2_tops_1(A_76, B_77))=k2_pre_topc(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.72/1.63  tff(c_834, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_830])).
% 3.72/1.63  tff(c_838, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_834])).
% 3.72/1.63  tff(c_179, plain, (![A_41, B_42, C_43]: (k7_subset_1(A_41, B_42, C_43)=k4_xboole_0(B_42, C_43) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.72/1.63  tff(c_183, plain, (![C_44]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_44)=k4_xboole_0('#skF_2', C_44))), inference(resolution, [status(thm)], [c_24, c_179])).
% 3.72/1.63  tff(c_189, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_183, c_156])).
% 3.72/1.63  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.72/1.63  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.72/1.63  tff(c_88, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.72/1.63  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.63  tff(c_100, plain, (![A_33, B_34]: (k2_xboole_0(k4_xboole_0(A_33, B_34), k3_xboole_0(A_33, B_34))=k2_xboole_0(k4_xboole_0(A_33, B_34), A_33))), inference(superposition, [status(thm), theory('equality')], [c_88, c_4])).
% 3.72/1.63  tff(c_269, plain, (![A_47, B_48]: (k2_xboole_0(k4_xboole_0(A_47, B_48), k3_xboole_0(A_47, B_48))=k2_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_100])).
% 3.72/1.63  tff(c_275, plain, (![A_47, B_48]: (k2_xboole_0(k3_xboole_0(A_47, B_48), k4_xboole_0(A_47, B_48))=k2_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_269, c_2])).
% 3.72/1.63  tff(c_315, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k4_xboole_0(A_49, B_50))=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_275])).
% 3.72/1.63  tff(c_331, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_189, c_315])).
% 3.72/1.63  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(k2_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.72/1.63  tff(c_446, plain, (![A_60, B_61, C_62]: (k4_subset_1(A_60, B_61, C_62)=k2_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.72/1.63  tff(c_1240, plain, (![A_97, B_98, B_99]: (k4_subset_1(u1_struct_0(A_97), B_98, k2_tops_1(A_97, B_99))=k2_xboole_0(B_98, k2_tops_1(A_97, B_99)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_18, c_446])).
% 3.72/1.63  tff(c_1244, plain, (![B_99]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_99))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1240])).
% 3.72/1.63  tff(c_1249, plain, (![B_100]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_100))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_100)) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1244])).
% 3.72/1.63  tff(c_1256, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1249])).
% 3.72/1.63  tff(c_1261, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_838, c_331, c_1256])).
% 3.72/1.63  tff(c_1263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_1261])).
% 3.72/1.63  tff(c_1265, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.72/1.63  tff(c_1291, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_1265])).
% 3.72/1.63  tff(c_1264, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.72/1.63  tff(c_1334, plain, (![A_109, B_110]: (k2_pre_topc(A_109, B_110)=B_110 | ~v4_pre_topc(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.63  tff(c_1337, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1334])).
% 3.72/1.63  tff(c_1340, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1264, c_1337])).
% 3.72/1.63  tff(c_1717, plain, (![A_141, B_142]: (k7_subset_1(u1_struct_0(A_141), k2_pre_topc(A_141, B_142), k1_tops_1(A_141, B_142))=k2_tops_1(A_141, B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.72/1.63  tff(c_1726, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1340, c_1717])).
% 3.72/1.63  tff(c_1730, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1290, c_1726])).
% 3.72/1.63  tff(c_1732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1291, c_1730])).
% 3.72/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.63  
% 3.72/1.63  Inference rules
% 3.72/1.63  ----------------------
% 3.72/1.63  #Ref     : 0
% 3.72/1.63  #Sup     : 451
% 3.72/1.63  #Fact    : 0
% 3.72/1.63  #Define  : 0
% 3.72/1.63  #Split   : 2
% 3.72/1.63  #Chain   : 0
% 3.72/1.63  #Close   : 0
% 3.72/1.63  
% 3.72/1.63  Ordering : KBO
% 3.72/1.63  
% 3.72/1.63  Simplification rules
% 3.72/1.63  ----------------------
% 3.72/1.63  #Subsume      : 2
% 3.72/1.63  #Demod        : 223
% 3.72/1.63  #Tautology    : 277
% 3.72/1.63  #SimpNegUnit  : 3
% 3.72/1.63  #BackRed      : 3
% 3.72/1.63  
% 3.72/1.63  #Partial instantiations: 0
% 3.72/1.63  #Strategies tried      : 1
% 3.72/1.63  
% 3.72/1.63  Timing (in seconds)
% 3.72/1.63  ----------------------
% 3.72/1.63  Preprocessing        : 0.32
% 3.72/1.63  Parsing              : 0.17
% 3.72/1.63  CNF conversion       : 0.02
% 3.72/1.63  Main loop            : 0.54
% 3.72/1.63  Inferencing          : 0.19
% 3.72/1.64  Reduction            : 0.21
% 3.72/1.64  Demodulation         : 0.17
% 3.72/1.64  BG Simplification    : 0.03
% 3.72/1.64  Subsumption          : 0.08
% 3.72/1.64  Abstraction          : 0.03
% 3.72/1.64  MUC search           : 0.00
% 3.72/1.64  Cooper               : 0.00
% 3.72/1.64  Total                : 0.89
% 3.72/1.64  Index Insertion      : 0.00
% 3.72/1.64  Index Deletion       : 0.00
% 3.72/1.64  Index Matching       : 0.00
% 3.72/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
