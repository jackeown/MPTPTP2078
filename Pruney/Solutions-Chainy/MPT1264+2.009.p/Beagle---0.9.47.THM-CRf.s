%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 212 expanded)
%              Number of leaves         :   34 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 474 expanded)
%              Number of equality atoms :   38 ( 120 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_68,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_73,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_77,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_30,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_102,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_30])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_34])).

tff(c_32,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(A_54,B_55,C_56) = k4_xboole_0(B_55,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_166,plain,(
    ! [C_56] : k7_subset_1(k2_struct_0('#skF_1'),'#skF_3',C_56) = k4_xboole_0('#skF_3',C_56) ),
    inference(resolution,[status(thm)],[c_79,c_159])).

tff(c_54,plain,(
    ! [A_39] :
      ( k1_struct_0(A_39) = k1_xboole_0
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    ! [A_40] :
      ( k1_struct_0(A_40) = k1_xboole_0
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_63,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_103,plain,(
    ! [A_46] :
      ( k3_subset_1(u1_struct_0(A_46),k1_struct_0(A_46)) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_112,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_103])).

tff(c_118,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_112])).

tff(c_120,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_123,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_120])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_123])).

tff(c_128,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_12,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_362,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(A_76,B_77,k3_subset_1(A_76,C_78)) = k7_subset_1(A_76,B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_372,plain,(
    ! [A_79,B_80] :
      ( k9_subset_1(A_79,B_80,k3_subset_1(A_79,k1_xboole_0)) = k7_subset_1(A_79,B_80,k1_xboole_0)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_12,c_362])).

tff(c_374,plain,(
    k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)) = k7_subset_1(k2_struct_0('#skF_1'),'#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_79,c_372])).

tff(c_380,plain,(
    k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_166,c_128,c_374])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_78,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_38])).

tff(c_36,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_316,plain,(
    ! [A_72,B_73] :
      ( k2_pre_topc(A_72,B_73) = k2_struct_0(A_72)
      | ~ v1_tops_1(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_319,plain,(
    ! [B_73] :
      ( k2_pre_topc('#skF_1',B_73) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_73,'#skF_1')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_316])).

tff(c_332,plain,(
    ! [B_75] :
      ( k2_pre_topc('#skF_1',B_75) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_75,'#skF_1')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_319])).

tff(c_338,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_332])).

tff(c_348,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_338])).

tff(c_395,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_pre_topc(A_82,k9_subset_1(u1_struct_0(A_82),B_83,k2_pre_topc(A_82,C_84))) = k2_pre_topc(A_82,k9_subset_1(u1_struct_0(A_82),B_83,C_84))
      | ~ v3_pre_topc(B_83,A_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_410,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_83,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_83,'#skF_2'))
      | ~ v3_pre_topc(B_83,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_395])).

tff(c_450,plain,(
    ! [B_87] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_87,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_87,'#skF_2'))
      | ~ v3_pre_topc(B_87,'#skF_1')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_77,c_78,c_77,c_77,c_77,c_410])).

tff(c_465,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_450])).

tff(c_476,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32,c_465])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.41  
% 2.62/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.41  %$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.41  
% 2.62/1.41  %Foreground sorts:
% 2.62/1.41  
% 2.62/1.41  
% 2.62/1.41  %Background operators:
% 2.62/1.41  
% 2.62/1.41  
% 2.62/1.41  %Foreground operators:
% 2.62/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.62/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.62/1.41  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.62/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.41  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.62/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.41  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.62/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.62/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.62/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.62/1.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.62/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.62/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.41  
% 2.88/1.43  tff(f_110, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 2.88/1.43  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.88/1.43  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.88/1.43  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.88/1.43  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.88/1.43  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.88/1.43  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.88/1.43  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.88/1.43  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 2.88/1.43  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.88/1.43  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 2.88/1.43  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_20, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.88/1.43  tff(c_68, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.88/1.43  tff(c_73, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_20, c_68])).
% 2.88/1.43  tff(c_77, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_73])).
% 2.88/1.43  tff(c_30, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_102, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_30])).
% 2.88/1.43  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_34])).
% 2.88/1.43  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.43  tff(c_159, plain, (![A_54, B_55, C_56]: (k7_subset_1(A_54, B_55, C_56)=k4_xboole_0(B_55, C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.43  tff(c_166, plain, (![C_56]: (k7_subset_1(k2_struct_0('#skF_1'), '#skF_3', C_56)=k4_xboole_0('#skF_3', C_56))), inference(resolution, [status(thm)], [c_79, c_159])).
% 2.88/1.43  tff(c_54, plain, (![A_39]: (k1_struct_0(A_39)=k1_xboole_0 | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.88/1.43  tff(c_59, plain, (![A_40]: (k1_struct_0(A_40)=k1_xboole_0 | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_20, c_54])).
% 2.88/1.43  tff(c_63, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_59])).
% 2.88/1.43  tff(c_103, plain, (![A_46]: (k3_subset_1(u1_struct_0(A_46), k1_struct_0(A_46))=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.88/1.43  tff(c_112, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_77, c_103])).
% 2.88/1.43  tff(c_118, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_112])).
% 2.88/1.43  tff(c_120, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_118])).
% 2.88/1.43  tff(c_123, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_120])).
% 2.88/1.43  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_123])).
% 2.88/1.43  tff(c_128, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_118])).
% 2.88/1.43  tff(c_12, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.88/1.43  tff(c_362, plain, (![A_76, B_77, C_78]: (k9_subset_1(A_76, B_77, k3_subset_1(A_76, C_78))=k7_subset_1(A_76, B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.88/1.43  tff(c_372, plain, (![A_79, B_80]: (k9_subset_1(A_79, B_80, k3_subset_1(A_79, k1_xboole_0))=k7_subset_1(A_79, B_80, k1_xboole_0) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(resolution, [status(thm)], [c_12, c_362])).
% 2.88/1.43  tff(c_374, plain, (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0))=k7_subset_1(k2_struct_0('#skF_1'), '#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_372])).
% 2.88/1.43  tff(c_380, plain, (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_166, c_128, c_374])).
% 2.88/1.43  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_78, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_38])).
% 2.88/1.43  tff(c_36, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.88/1.43  tff(c_316, plain, (![A_72, B_73]: (k2_pre_topc(A_72, B_73)=k2_struct_0(A_72) | ~v1_tops_1(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.43  tff(c_319, plain, (![B_73]: (k2_pre_topc('#skF_1', B_73)=k2_struct_0('#skF_1') | ~v1_tops_1(B_73, '#skF_1') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_316])).
% 2.88/1.43  tff(c_332, plain, (![B_75]: (k2_pre_topc('#skF_1', B_75)=k2_struct_0('#skF_1') | ~v1_tops_1(B_75, '#skF_1') | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_319])).
% 2.88/1.43  tff(c_338, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_332])).
% 2.88/1.43  tff(c_348, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_338])).
% 2.88/1.43  tff(c_395, plain, (![A_82, B_83, C_84]: (k2_pre_topc(A_82, k9_subset_1(u1_struct_0(A_82), B_83, k2_pre_topc(A_82, C_84)))=k2_pre_topc(A_82, k9_subset_1(u1_struct_0(A_82), B_83, C_84)) | ~v3_pre_topc(B_83, A_82) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.88/1.43  tff(c_410, plain, (![B_83]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_83, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_83, '#skF_2')) | ~v3_pre_topc(B_83, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_395])).
% 2.88/1.43  tff(c_450, plain, (![B_87]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_87, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_87, '#skF_2')) | ~v3_pre_topc(B_87, '#skF_1') | ~m1_subset_1(B_87, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_77, c_78, c_77, c_77, c_77, c_410])).
% 2.88/1.43  tff(c_465, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_380, c_450])).
% 2.88/1.43  tff(c_476, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32, c_465])).
% 2.88/1.43  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_476])).
% 2.88/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.43  
% 2.88/1.43  Inference rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Ref     : 1
% 2.88/1.43  #Sup     : 100
% 2.88/1.43  #Fact    : 0
% 2.88/1.43  #Define  : 0
% 2.88/1.43  #Split   : 3
% 2.88/1.43  #Chain   : 0
% 2.88/1.43  #Close   : 0
% 2.88/1.43  
% 2.88/1.43  Ordering : KBO
% 2.88/1.43  
% 2.88/1.43  Simplification rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Subsume      : 2
% 2.88/1.43  #Demod        : 45
% 2.88/1.43  #Tautology    : 59
% 2.88/1.43  #SimpNegUnit  : 3
% 2.88/1.43  #BackRed      : 2
% 2.88/1.43  
% 2.88/1.43  #Partial instantiations: 0
% 2.88/1.43  #Strategies tried      : 1
% 2.88/1.43  
% 2.88/1.43  Timing (in seconds)
% 2.88/1.43  ----------------------
% 2.88/1.43  Preprocessing        : 0.33
% 2.88/1.43  Parsing              : 0.19
% 2.88/1.43  CNF conversion       : 0.02
% 2.88/1.43  Main loop            : 0.28
% 2.88/1.43  Inferencing          : 0.11
% 2.88/1.43  Reduction            : 0.09
% 2.88/1.43  Demodulation         : 0.07
% 2.88/1.43  BG Simplification    : 0.02
% 2.88/1.43  Subsumption          : 0.04
% 2.88/1.43  Abstraction          : 0.02
% 2.88/1.43  MUC search           : 0.00
% 2.88/1.43  Cooper               : 0.00
% 2.88/1.43  Total                : 0.64
% 2.88/1.43  Index Insertion      : 0.00
% 2.88/1.43  Index Deletion       : 0.00
% 2.88/1.43  Index Matching       : 0.00
% 2.88/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
