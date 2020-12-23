%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:28 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   63 (  86 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 238 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
      <=> v1_xboole_0(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_86,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    ! [A_21] :
      ( u1_struct_0(A_21) = k2_struct_0(A_21)
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_52])).

tff(c_61,plain,(
    ! [A_22] :
      ( v2_struct_0(A_22)
      | ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,
    ( v2_struct_0('#skF_1')
    | ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_61])).

tff(c_66,plain,
    ( v2_struct_0('#skF_1')
    | ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_64])).

tff(c_67,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_66])).

tff(c_32,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,k1_tarski(B_3)) = A_2
      | r2_hidden(B_3,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [A_28,B_29,C_30] :
      ( k7_subset_1(A_28,B_29,C_30) = k4_xboole_0(B_29,C_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [C_30] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_30) = k4_xboole_0('#skF_2',C_30) ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_110,plain,(
    ! [A_37,B_38] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_37))),B_38,k1_tarski(k1_xboole_0)) = k2_yellow19(A_37,k3_yellow19(A_37,k2_struct_0(A_37),B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_37)))))
      | ~ v13_waybel_0(B_38,k3_yellow_1(k2_struct_0(A_37)))
      | ~ v2_waybel_0(B_38,k3_yellow_1(k2_struct_0(A_37)))
      | v1_xboole_0(B_38)
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_112,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_115,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_98,c_112])).

tff(c_116,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_115])).

tff(c_24,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_117,plain,(
    k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_24])).

tff(c_125,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_117])).

tff(c_22,plain,(
    ! [C_18,B_16,A_12] :
      ( ~ v1_xboole_0(C_18)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_12))))
      | ~ v13_waybel_0(B_16,k3_yellow_1(A_12))
      | ~ v2_waybel_0(B_16,k3_yellow_1(A_12))
      | ~ v1_subset_1(B_16,u1_struct_0(k3_yellow_1(A_12)))
      | v1_xboole_0(B_16)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_127,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_12))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_12))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_12))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_12)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_125,c_22])).

tff(c_130,plain,(
    ! [A_12] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_12))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_12))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_12))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_12)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_132,plain,(
    ! [A_39] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_39))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_39))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_39)))
      | v1_xboole_0(A_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_130])).

tff(c_135,plain,
    ( ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_132])).

tff(c_138,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_135])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.36  
% 2.20/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.36  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.20/1.36  
% 2.20/1.36  %Foreground sorts:
% 2.20/1.36  
% 2.20/1.36  
% 2.20/1.36  %Background operators:
% 2.20/1.36  
% 2.20/1.36  
% 2.20/1.36  %Foreground operators:
% 2.20/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.36  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.20/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.36  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.20/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.36  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.20/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.36  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.20/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.20/1.36  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.20/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.36  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.20/1.36  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.20/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.20/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.36  
% 2.36/1.38  tff(f_106, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.36/1.38  tff(f_42, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.36/1.38  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (v2_struct_0(A) <=> v1_xboole_0(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_struct_0)).
% 2.36/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.36/1.38  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.36/1.38  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.36/1.38  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.36/1.38  tff(f_86, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.36/1.38  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_36, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_52, plain, (![A_21]: (u1_struct_0(A_21)=k2_struct_0(A_21) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.38  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_52])).
% 2.36/1.38  tff(c_61, plain, (![A_22]: (v2_struct_0(A_22) | ~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.38  tff(c_64, plain, (v2_struct_0('#skF_1') | ~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_61])).
% 2.36/1.38  tff(c_66, plain, (v2_struct_0('#skF_1') | ~v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_64])).
% 2.36/1.38  tff(c_67, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_38, c_66])).
% 2.36/1.38  tff(c_32, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_30, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_28, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.36/1.38  tff(c_10, plain, (![A_2, B_3]: (k4_xboole_0(A_2, k1_tarski(B_3))=A_2 | r2_hidden(B_3, A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.38  tff(c_93, plain, (![A_28, B_29, C_30]: (k7_subset_1(A_28, B_29, C_30)=k4_xboole_0(B_29, C_30) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.36/1.38  tff(c_98, plain, (![C_30]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', C_30)=k4_xboole_0('#skF_2', C_30))), inference(resolution, [status(thm)], [c_26, c_93])).
% 2.36/1.38  tff(c_110, plain, (![A_37, B_38]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_37))), B_38, k1_tarski(k1_xboole_0))=k2_yellow19(A_37, k3_yellow19(A_37, k2_struct_0(A_37), B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_37))))) | ~v13_waybel_0(B_38, k3_yellow_1(k2_struct_0(A_37))) | ~v2_waybel_0(B_38, k3_yellow_1(k2_struct_0(A_37))) | v1_xboole_0(B_38) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.38  tff(c_112, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_110])).
% 2.36/1.38  tff(c_115, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_28, c_98, c_112])).
% 2.36/1.38  tff(c_116, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_115])).
% 2.36/1.38  tff(c_24, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.38  tff(c_117, plain, (k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_24])).
% 2.36/1.38  tff(c_125, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_117])).
% 2.36/1.38  tff(c_22, plain, (![C_18, B_16, A_12]: (~v1_xboole_0(C_18) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_12)))) | ~v13_waybel_0(B_16, k3_yellow_1(A_12)) | ~v2_waybel_0(B_16, k3_yellow_1(A_12)) | ~v1_subset_1(B_16, u1_struct_0(k3_yellow_1(A_12))) | v1_xboole_0(B_16) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.36/1.38  tff(c_127, plain, (![A_12]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_12)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_12)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_12)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_12))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_125, c_22])).
% 2.36/1.38  tff(c_130, plain, (![A_12]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_12)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_12)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_12)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_12))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 2.36/1.38  tff(c_132, plain, (![A_39]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_39)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_39)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_39))) | v1_xboole_0(A_39))), inference(negUnitSimplification, [status(thm)], [c_34, c_130])).
% 2.36/1.38  tff(c_135, plain, (~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_132])).
% 2.36/1.38  tff(c_138, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_135])).
% 2.36/1.38  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_138])).
% 2.36/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.38  
% 2.36/1.38  Inference rules
% 2.36/1.38  ----------------------
% 2.36/1.38  #Ref     : 0
% 2.36/1.38  #Sup     : 23
% 2.36/1.38  #Fact    : 0
% 2.36/1.38  #Define  : 0
% 2.36/1.38  #Split   : 0
% 2.36/1.38  #Chain   : 0
% 2.36/1.38  #Close   : 0
% 2.36/1.38  
% 2.36/1.38  Ordering : KBO
% 2.36/1.38  
% 2.36/1.38  Simplification rules
% 2.36/1.38  ----------------------
% 2.36/1.38  #Subsume      : 1
% 2.36/1.38  #Demod        : 11
% 2.36/1.38  #Tautology    : 14
% 2.36/1.38  #SimpNegUnit  : 5
% 2.36/1.38  #BackRed      : 1
% 2.36/1.38  
% 2.36/1.38  #Partial instantiations: 0
% 2.36/1.38  #Strategies tried      : 1
% 2.36/1.38  
% 2.36/1.38  Timing (in seconds)
% 2.36/1.38  ----------------------
% 2.36/1.38  Preprocessing        : 0.42
% 2.36/1.38  Parsing              : 0.23
% 2.36/1.38  CNF conversion       : 0.02
% 2.36/1.38  Main loop            : 0.18
% 2.36/1.38  Inferencing          : 0.06
% 2.36/1.38  Reduction            : 0.06
% 2.36/1.38  Demodulation         : 0.05
% 2.36/1.38  BG Simplification    : 0.01
% 2.36/1.38  Subsumption          : 0.03
% 2.36/1.39  Abstraction          : 0.02
% 2.36/1.39  MUC search           : 0.00
% 2.36/1.39  Cooper               : 0.00
% 2.36/1.39  Total                : 0.65
% 2.36/1.39  Index Insertion      : 0.00
% 2.36/1.39  Index Deletion       : 0.00
% 2.36/1.39  Index Matching       : 0.00
% 2.36/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
