%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:28 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 164 expanded)
%              Number of leaves         :   40 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  127 ( 492 expanded)
%              Number of equality atoms :   21 (  82 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_94,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_115,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_195,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_198,plain,(
    ! [C_68] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',C_68) = k4_xboole_0('#skF_6',C_68) ),
    inference(resolution,[status(thm)],[c_44,c_195])).

tff(c_1673,plain,(
    ! [A_4740,B_4741] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_4740))),B_4741,k1_tarski(k1_xboole_0)) = k2_yellow19(A_4740,k3_yellow19(A_4740,k2_struct_0(A_4740),B_4741))
      | ~ m1_subset_1(B_4741,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_4740)))))
      | ~ v13_waybel_0(B_4741,k3_yellow_1(k2_struct_0(A_4740)))
      | ~ v2_waybel_0(B_4741,k3_yellow_1(k2_struct_0(A_4740)))
      | v1_xboole_0(B_4741)
      | ~ l1_struct_0(A_4740)
      | v2_struct_0(A_4740) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1706,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1673])).

tff(c_1709,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_198,c_1706])).

tff(c_1710,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_1709])).

tff(c_42,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1711,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1710,c_42])).

tff(c_121,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),B_50)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_199,plain,(
    ! [A_69,A_70] :
      ( '#skF_2'(A_69,k1_tarski(A_70)) = A_70
      | r1_xboole_0(A_69,k1_tarski(A_70)) ) ),
    inference(resolution,[status(thm)],[c_121,c_18])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_206,plain,(
    ! [A_69,A_70] :
      ( k4_xboole_0(A_69,k1_tarski(A_70)) = A_69
      | '#skF_2'(A_69,k1_tarski(A_70)) = A_70 ) ),
    inference(resolution,[status(thm)],[c_199,c_14])).

tff(c_1756,plain,(
    '#skF_2'('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_1711])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1763,plain,
    ( r2_hidden(k1_xboole_0,'#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_12])).

tff(c_1849,plain,(
    r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1763])).

tff(c_1854,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1849,c_14])).

tff(c_1899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1711,c_1854])).

tff(c_1900,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1763])).

tff(c_40,plain,(
    ! [C_32,B_30,A_26] :
      ( ~ v1_xboole_0(C_32)
      | ~ r2_hidden(C_32,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_26))))
      | ~ v13_waybel_0(B_30,k3_yellow_1(A_26))
      | ~ v2_waybel_0(B_30,k3_yellow_1(A_26))
      | ~ v1_subset_1(B_30,u1_struct_0(k3_yellow_1(A_26)))
      | v1_xboole_0(B_30)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1906,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_26))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_26))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_26))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_26)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_1900,c_40])).

tff(c_1915,plain,(
    ! [A_26] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_26))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_26))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_26))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_26)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1906])).

tff(c_4929,plain,(
    ! [A_9018] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_9018))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_9018))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_9018))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_9018)))
      | v1_xboole_0(A_9018) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1915])).

tff(c_4938,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_4929])).

tff(c_4941,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_4938])).

tff(c_34,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k2_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4952,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4941,c_34])).

tff(c_4961,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4952])).

tff(c_4963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.89  
% 4.71/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.90  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.71/1.90  
% 4.71/1.90  %Foreground sorts:
% 4.71/1.90  
% 4.71/1.90  
% 4.71/1.90  %Background operators:
% 4.71/1.90  
% 4.71/1.90  
% 4.71/1.90  %Foreground operators:
% 4.71/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.71/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.90  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.71/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.90  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.71/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.71/1.90  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.71/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.71/1.90  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.71/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.90  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.71/1.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.71/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.71/1.90  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.71/1.90  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.71/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.71/1.90  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.71/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.71/1.90  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.71/1.90  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.71/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.71/1.90  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.71/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.71/1.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.71/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.90  
% 4.71/1.91  tff(f_135, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 4.71/1.91  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.71/1.91  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.71/1.91  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 4.71/1.91  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.71/1.91  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.71/1.91  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.71/1.91  tff(f_115, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 4.71/1.91  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 4.71/1.91  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_54, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_50, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_48, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_46, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_52, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.71/1.91  tff(c_195, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.71/1.91  tff(c_198, plain, (![C_68]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', C_68)=k4_xboole_0('#skF_6', C_68))), inference(resolution, [status(thm)], [c_44, c_195])).
% 4.71/1.91  tff(c_1673, plain, (![A_4740, B_4741]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_4740))), B_4741, k1_tarski(k1_xboole_0))=k2_yellow19(A_4740, k3_yellow19(A_4740, k2_struct_0(A_4740), B_4741)) | ~m1_subset_1(B_4741, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_4740))))) | ~v13_waybel_0(B_4741, k3_yellow_1(k2_struct_0(A_4740))) | ~v2_waybel_0(B_4741, k3_yellow_1(k2_struct_0(A_4740))) | v1_xboole_0(B_4741) | ~l1_struct_0(A_4740) | v2_struct_0(A_4740))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.71/1.91  tff(c_1706, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1673])).
% 4.71/1.91  tff(c_1709, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_198, c_1706])).
% 4.71/1.91  tff(c_1710, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_1709])).
% 4.71/1.91  tff(c_42, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.91  tff(c_1711, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1710, c_42])).
% 4.71/1.91  tff(c_121, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), B_50) | r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.71/1.91  tff(c_18, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.71/1.91  tff(c_199, plain, (![A_69, A_70]: ('#skF_2'(A_69, k1_tarski(A_70))=A_70 | r1_xboole_0(A_69, k1_tarski(A_70)))), inference(resolution, [status(thm)], [c_121, c_18])).
% 4.71/1.91  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.71/1.91  tff(c_206, plain, (![A_69, A_70]: (k4_xboole_0(A_69, k1_tarski(A_70))=A_69 | '#skF_2'(A_69, k1_tarski(A_70))=A_70)), inference(resolution, [status(thm)], [c_199, c_14])).
% 4.71/1.91  tff(c_1756, plain, ('#skF_2'('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_206, c_1711])).
% 4.71/1.91  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.71/1.91  tff(c_1763, plain, (r2_hidden(k1_xboole_0, '#skF_6') | r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1756, c_12])).
% 4.71/1.91  tff(c_1849, plain, (r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1763])).
% 4.71/1.91  tff(c_1854, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))='#skF_6'), inference(resolution, [status(thm)], [c_1849, c_14])).
% 4.71/1.91  tff(c_1899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1711, c_1854])).
% 4.71/1.91  tff(c_1900, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_1763])).
% 4.71/1.91  tff(c_40, plain, (![C_32, B_30, A_26]: (~v1_xboole_0(C_32) | ~r2_hidden(C_32, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_26)))) | ~v13_waybel_0(B_30, k3_yellow_1(A_26)) | ~v2_waybel_0(B_30, k3_yellow_1(A_26)) | ~v1_subset_1(B_30, u1_struct_0(k3_yellow_1(A_26))) | v1_xboole_0(B_30) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.71/1.91  tff(c_1906, plain, (![A_26]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_26)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_26)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_26)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_26))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_1900, c_40])).
% 4.71/1.91  tff(c_1915, plain, (![A_26]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_26)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_26)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_26)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_26))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1906])).
% 4.71/1.91  tff(c_4929, plain, (![A_9018]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_9018)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_9018)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_9018)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_9018))) | v1_xboole_0(A_9018))), inference(negUnitSimplification, [status(thm)], [c_52, c_1915])).
% 4.71/1.91  tff(c_4938, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_4929])).
% 4.71/1.91  tff(c_4941, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_4938])).
% 4.71/1.91  tff(c_34, plain, (![A_21]: (~v1_xboole_0(k2_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.71/1.91  tff(c_4952, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4941, c_34])).
% 4.71/1.91  tff(c_4961, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4952])).
% 4.71/1.91  tff(c_4963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_4961])).
% 4.71/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.91  
% 4.71/1.91  Inference rules
% 4.71/1.91  ----------------------
% 4.71/1.91  #Ref     : 0
% 4.71/1.91  #Sup     : 710
% 4.71/1.91  #Fact    : 4
% 4.71/1.91  #Define  : 0
% 4.71/1.91  #Split   : 5
% 4.71/1.91  #Chain   : 0
% 4.71/1.91  #Close   : 0
% 4.71/1.91  
% 4.71/1.91  Ordering : KBO
% 4.71/1.91  
% 4.71/1.91  Simplification rules
% 4.71/1.91  ----------------------
% 4.71/1.91  #Subsume      : 130
% 4.71/1.91  #Demod        : 291
% 4.71/1.91  #Tautology    : 296
% 4.71/1.91  #SimpNegUnit  : 59
% 4.71/1.91  #BackRed      : 16
% 4.71/1.91  
% 4.71/1.91  #Partial instantiations: 3870
% 4.71/1.91  #Strategies tried      : 1
% 4.71/1.91  
% 4.71/1.91  Timing (in seconds)
% 4.71/1.91  ----------------------
% 4.71/1.91  Preprocessing        : 0.34
% 4.71/1.91  Parsing              : 0.18
% 4.71/1.91  CNF conversion       : 0.02
% 4.71/1.91  Main loop            : 0.81
% 4.71/1.91  Inferencing          : 0.38
% 4.71/1.91  Reduction            : 0.21
% 4.71/1.91  Demodulation         : 0.14
% 4.71/1.91  BG Simplification    : 0.03
% 4.71/1.91  Subsumption          : 0.13
% 4.71/1.91  Abstraction          : 0.04
% 4.71/1.91  MUC search           : 0.00
% 4.71/1.91  Cooper               : 0.00
% 4.71/1.91  Total                : 1.17
% 4.71/1.91  Index Insertion      : 0.00
% 4.71/1.91  Index Deletion       : 0.00
% 4.71/1.91  Index Matching       : 0.00
% 4.71/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
