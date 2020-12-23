%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:31 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   71 (  94 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 250 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

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

tff(f_115,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_95,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_58,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(u1_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_58])).

tff(c_63,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_61])).

tff(c_64,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_63])).

tff(c_32,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_28,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(k1_tarski(A_31),B_32)
      | r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_82,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,k1_tarski(A_36))
      | r2_hidden(A_36,B_35) ) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [B_35,A_36] :
      ( k4_xboole_0(B_35,k1_tarski(A_36)) = B_35
      | r2_hidden(A_36,B_35) ) ),
    inference(resolution,[status(thm)],[c_82,c_6])).

tff(c_133,plain,(
    ! [A_45,B_46,C_47] :
      ( k7_subset_1(A_45,B_46,C_47) = k4_xboole_0(B_46,C_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [C_47] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_47) = k4_xboole_0('#skF_2',C_47) ),
    inference(resolution,[status(thm)],[c_26,c_133])).

tff(c_147,plain,(
    ! [A_52,B_53] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_52))),B_53,k1_tarski(k1_xboole_0)) = k2_yellow19(A_52,k3_yellow19(A_52,k2_struct_0(A_52),B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_52)))))
      | ~ v13_waybel_0(B_53,k3_yellow_1(k2_struct_0(A_52)))
      | ~ v2_waybel_0(B_53,k3_yellow_1(k2_struct_0(A_52)))
      | v1_xboole_0(B_53)
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_149,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_152,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_136,c_149])).

tff(c_153,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_152])).

tff(c_24,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_154,plain,(
    k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_24])).

tff(c_162,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_154])).

tff(c_22,plain,(
    ! [C_22,B_20,A_16] :
      ( ~ v1_xboole_0(C_22)
      | ~ r2_hidden(C_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_16))))
      | ~ v13_waybel_0(B_20,k3_yellow_1(A_16))
      | ~ v2_waybel_0(B_20,k3_yellow_1(A_16))
      | ~ v1_subset_1(B_20,u1_struct_0(k3_yellow_1(A_16)))
      | v1_xboole_0(B_20)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_164,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_16))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_16))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_16))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_16)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_162,c_22])).

tff(c_167,plain,(
    ! [A_16] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_16))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_16))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_16))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_16)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_164])).

tff(c_169,plain,(
    ! [A_54] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_54))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_54))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_54))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_54)))
      | v1_xboole_0(A_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_167])).

tff(c_172,plain,
    ( ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_175,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_172])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:44:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.42  
% 2.09/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.42  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.42  
% 2.09/1.42  %Foreground sorts:
% 2.09/1.42  
% 2.09/1.42  
% 2.09/1.42  %Background operators:
% 2.09/1.42  
% 2.09/1.42  
% 2.09/1.42  %Foreground operators:
% 2.09/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.09/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.42  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.09/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.09/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.42  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.09/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.42  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.09/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.42  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.09/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.42  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.09/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.09/1.42  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.09/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.42  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.09/1.42  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.09/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.09/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.42  
% 2.09/1.43  tff(f_115, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.09/1.43  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.09/1.43  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.09/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.09/1.43  tff(f_39, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.09/1.43  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.09/1.43  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.09/1.43  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.09/1.43  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.09/1.43  tff(f_95, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.09/1.43  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_36, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_48, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.43  tff(c_52, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_48])).
% 2.09/1.43  tff(c_58, plain, (![A_28]: (~v1_xboole_0(u1_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.43  tff(c_61, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_52, c_58])).
% 2.09/1.43  tff(c_63, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_61])).
% 2.09/1.43  tff(c_64, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_38, c_63])).
% 2.09/1.43  tff(c_32, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_30, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_28, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.09/1.43  tff(c_66, plain, (![A_31, B_32]: (r1_xboole_0(k1_tarski(A_31), B_32) | r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.43  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.09/1.43  tff(c_82, plain, (![B_35, A_36]: (r1_xboole_0(B_35, k1_tarski(A_36)) | r2_hidden(A_36, B_35))), inference(resolution, [status(thm)], [c_66, c_4])).
% 2.09/1.43  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.43  tff(c_88, plain, (![B_35, A_36]: (k4_xboole_0(B_35, k1_tarski(A_36))=B_35 | r2_hidden(A_36, B_35))), inference(resolution, [status(thm)], [c_82, c_6])).
% 2.09/1.43  tff(c_133, plain, (![A_45, B_46, C_47]: (k7_subset_1(A_45, B_46, C_47)=k4_xboole_0(B_46, C_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.43  tff(c_136, plain, (![C_47]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', C_47)=k4_xboole_0('#skF_2', C_47))), inference(resolution, [status(thm)], [c_26, c_133])).
% 2.09/1.43  tff(c_147, plain, (![A_52, B_53]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_52))), B_53, k1_tarski(k1_xboole_0))=k2_yellow19(A_52, k3_yellow19(A_52, k2_struct_0(A_52), B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_52))))) | ~v13_waybel_0(B_53, k3_yellow_1(k2_struct_0(A_52))) | ~v2_waybel_0(B_53, k3_yellow_1(k2_struct_0(A_52))) | v1_xboole_0(B_53) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.43  tff(c_149, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_147])).
% 2.09/1.43  tff(c_152, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_28, c_136, c_149])).
% 2.09/1.43  tff(c_153, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_152])).
% 2.09/1.43  tff(c_24, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.09/1.43  tff(c_154, plain, (k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_24])).
% 2.09/1.43  tff(c_162, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_154])).
% 2.09/1.43  tff(c_22, plain, (![C_22, B_20, A_16]: (~v1_xboole_0(C_22) | ~r2_hidden(C_22, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_16)))) | ~v13_waybel_0(B_20, k3_yellow_1(A_16)) | ~v2_waybel_0(B_20, k3_yellow_1(A_16)) | ~v1_subset_1(B_20, u1_struct_0(k3_yellow_1(A_16))) | v1_xboole_0(B_20) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.09/1.43  tff(c_164, plain, (![A_16]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_16)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_16)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_16)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_16))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_162, c_22])).
% 2.09/1.43  tff(c_167, plain, (![A_16]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_16)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_16)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_16)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_16))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_164])).
% 2.09/1.43  tff(c_169, plain, (![A_54]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_54)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_54)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_54)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_54))) | v1_xboole_0(A_54))), inference(negUnitSimplification, [status(thm)], [c_34, c_167])).
% 2.09/1.43  tff(c_172, plain, (~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_169])).
% 2.09/1.43  tff(c_175, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_172])).
% 2.09/1.43  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_175])).
% 2.09/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.43  
% 2.09/1.43  Inference rules
% 2.09/1.43  ----------------------
% 2.09/1.43  #Ref     : 0
% 2.09/1.43  #Sup     : 31
% 2.09/1.43  #Fact    : 0
% 2.09/1.43  #Define  : 0
% 2.09/1.43  #Split   : 0
% 2.09/1.43  #Chain   : 0
% 2.09/1.43  #Close   : 0
% 2.09/1.43  
% 2.09/1.43  Ordering : KBO
% 2.09/1.43  
% 2.09/1.43  Simplification rules
% 2.09/1.43  ----------------------
% 2.09/1.43  #Subsume      : 4
% 2.09/1.43  #Demod        : 10
% 2.09/1.43  #Tautology    : 15
% 2.09/1.43  #SimpNegUnit  : 4
% 2.09/1.43  #BackRed      : 1
% 2.09/1.43  
% 2.09/1.43  #Partial instantiations: 0
% 2.09/1.43  #Strategies tried      : 1
% 2.09/1.43  
% 2.09/1.43  Timing (in seconds)
% 2.09/1.43  ----------------------
% 2.09/1.44  Preprocessing        : 0.38
% 2.09/1.44  Parsing              : 0.22
% 2.09/1.44  CNF conversion       : 0.02
% 2.09/1.44  Main loop            : 0.16
% 2.09/1.44  Inferencing          : 0.07
% 2.09/1.44  Reduction            : 0.05
% 2.09/1.44  Demodulation         : 0.04
% 2.09/1.44  BG Simplification    : 0.01
% 2.09/1.44  Subsumption          : 0.02
% 2.09/1.44  Abstraction          : 0.01
% 2.09/1.44  MUC search           : 0.00
% 2.09/1.44  Cooper               : 0.00
% 2.09/1.44  Total                : 0.58
% 2.09/1.44  Index Insertion      : 0.00
% 2.09/1.44  Index Deletion       : 0.00
% 2.09/1.44  Index Matching       : 0.00
% 2.09/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
