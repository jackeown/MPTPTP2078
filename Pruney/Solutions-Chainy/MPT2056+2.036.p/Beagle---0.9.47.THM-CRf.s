%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:30 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 167 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 502 expanded)
%              Number of equality atoms :   21 (  82 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_116,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_194,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_subset_1(A_67,B_68,C_69) = k4_xboole_0(B_68,C_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_197,plain,(
    ! [C_69] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_69) = k4_xboole_0('#skF_4',C_69) ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_388,plain,(
    ! [A_93,B_94] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_93))),B_94,k1_tarski(k1_xboole_0)) = k2_yellow19(A_93,k3_yellow19(A_93,k2_struct_0(A_93),B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_93)))))
      | ~ v13_waybel_0(B_94,k3_yellow_1(k2_struct_0(A_93)))
      | ~ v2_waybel_0(B_94,k3_yellow_1(k2_struct_0(A_93)))
      | v1_xboole_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_390,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_388])).

tff(c_393,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_197,c_390])).

tff(c_394,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_393])).

tff(c_32,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_433,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_32])).

tff(c_91,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_2'(A_48,B_49),B_49)
      | r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,B_39)
      | ~ r1_xboole_0(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_310,plain,(
    ! [A_85,B_86] :
      ( '#skF_2'(A_85,k1_tarski(B_86)) = B_86
      | r1_xboole_0(A_85,k1_tarski(B_86)) ) ),
    inference(resolution,[status(thm)],[c_91,c_67])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_580,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(A_113,k1_tarski(B_114)) = A_113
      | '#skF_2'(A_113,k1_tarski(B_114)) = B_114 ) ),
    inference(resolution,[status(thm)],[c_310,c_14])).

tff(c_625,plain,(
    '#skF_2'('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_433])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_640,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_12])).

tff(c_648,plain,(
    r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_640])).

tff(c_661,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_648,c_14])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_661])).

tff(c_667,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_640])).

tff(c_30,plain,(
    ! [C_30,B_28,A_24] :
      ( ~ v1_xboole_0(C_30)
      | ~ r2_hidden(C_30,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24))))
      | ~ v13_waybel_0(B_28,k3_yellow_1(A_24))
      | ~ v2_waybel_0(B_28,k3_yellow_1(A_24))
      | ~ v1_subset_1(B_28,u1_struct_0(k3_yellow_1(A_24)))
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_674,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_24))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_24))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_24)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_667,c_30])).

tff(c_685,plain,(
    ! [A_24] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_24))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_24))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_24)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_674])).

tff(c_711,plain,(
    ! [A_117] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_117))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_117))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_117))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_117)))
      | v1_xboole_0(A_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_685])).

tff(c_714,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_711])).

tff(c_717,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_714])).

tff(c_24,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_724,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_717,c_24])).

tff(c_729,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_724])).

tff(c_731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.40  
% 2.85/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.40  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.85/1.40  
% 2.85/1.40  %Foreground sorts:
% 2.85/1.40  
% 2.85/1.40  
% 2.85/1.40  %Background operators:
% 2.85/1.40  
% 2.85/1.40  
% 2.85/1.40  %Foreground operators:
% 2.85/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.85/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.40  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.85/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.85/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.40  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.85/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.85/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.40  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.85/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.40  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.85/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.40  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.85/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.85/1.40  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.85/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.40  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.85/1.40  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.85/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.85/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.40  
% 2.85/1.42  tff(f_136, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.85/1.42  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/1.42  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.85/1.42  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.85/1.42  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.85/1.42  tff(f_64, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.85/1.42  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.85/1.42  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.85/1.42  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.85/1.42  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.85/1.42  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_44, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_40, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_38, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_36, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.42  tff(c_194, plain, (![A_67, B_68, C_69]: (k7_subset_1(A_67, B_68, C_69)=k4_xboole_0(B_68, C_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.42  tff(c_197, plain, (![C_69]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_69)=k4_xboole_0('#skF_4', C_69))), inference(resolution, [status(thm)], [c_34, c_194])).
% 2.85/1.42  tff(c_388, plain, (![A_93, B_94]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_93))), B_94, k1_tarski(k1_xboole_0))=k2_yellow19(A_93, k3_yellow19(A_93, k2_struct_0(A_93), B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_93))))) | ~v13_waybel_0(B_94, k3_yellow_1(k2_struct_0(A_93))) | ~v2_waybel_0(B_94, k3_yellow_1(k2_struct_0(A_93))) | v1_xboole_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.42  tff(c_390, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_388])).
% 2.85/1.42  tff(c_393, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_197, c_390])).
% 2.85/1.42  tff(c_394, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_393])).
% 2.85/1.42  tff(c_32, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.42  tff(c_433, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_32])).
% 2.85/1.42  tff(c_91, plain, (![A_48, B_49]: (r2_hidden('#skF_2'(A_48, B_49), B_49) | r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.42  tff(c_20, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), k1_tarski(B_15)) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.85/1.42  tff(c_63, plain, (![A_38, B_39]: (~r2_hidden(A_38, B_39) | ~r1_xboole_0(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.42  tff(c_67, plain, (![A_14, B_15]: (~r2_hidden(A_14, k1_tarski(B_15)) | B_15=A_14)), inference(resolution, [status(thm)], [c_20, c_63])).
% 2.85/1.42  tff(c_310, plain, (![A_85, B_86]: ('#skF_2'(A_85, k1_tarski(B_86))=B_86 | r1_xboole_0(A_85, k1_tarski(B_86)))), inference(resolution, [status(thm)], [c_91, c_67])).
% 2.85/1.42  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/1.42  tff(c_580, plain, (![A_113, B_114]: (k4_xboole_0(A_113, k1_tarski(B_114))=A_113 | '#skF_2'(A_113, k1_tarski(B_114))=B_114)), inference(resolution, [status(thm)], [c_310, c_14])).
% 2.85/1.42  tff(c_625, plain, ('#skF_2'('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_580, c_433])).
% 2.85/1.42  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.42  tff(c_640, plain, (r2_hidden(k1_xboole_0, '#skF_4') | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_625, c_12])).
% 2.85/1.42  tff(c_648, plain, (r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_640])).
% 2.85/1.42  tff(c_661, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))='#skF_4'), inference(resolution, [status(thm)], [c_648, c_14])).
% 2.85/1.42  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_433, c_661])).
% 2.85/1.42  tff(c_667, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_640])).
% 2.85/1.42  tff(c_30, plain, (![C_30, B_28, A_24]: (~v1_xboole_0(C_30) | ~r2_hidden(C_30, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24)))) | ~v13_waybel_0(B_28, k3_yellow_1(A_24)) | ~v2_waybel_0(B_28, k3_yellow_1(A_24)) | ~v1_subset_1(B_28, u1_struct_0(k3_yellow_1(A_24))) | v1_xboole_0(B_28) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.85/1.42  tff(c_674, plain, (![A_24]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_24)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_24)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_24))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_667, c_30])).
% 2.85/1.42  tff(c_685, plain, (![A_24]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_24)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_24)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_24)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_24))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_674])).
% 2.85/1.42  tff(c_711, plain, (![A_117]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_117)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_117)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_117)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_117))) | v1_xboole_0(A_117))), inference(negUnitSimplification, [status(thm)], [c_42, c_685])).
% 2.85/1.42  tff(c_714, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_711])).
% 2.85/1.42  tff(c_717, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_714])).
% 2.85/1.42  tff(c_24, plain, (![A_19]: (~v1_xboole_0(k2_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.85/1.42  tff(c_724, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_717, c_24])).
% 2.85/1.42  tff(c_729, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_724])).
% 2.85/1.42  tff(c_731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_729])).
% 2.85/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.42  
% 2.85/1.42  Inference rules
% 2.85/1.42  ----------------------
% 2.85/1.42  #Ref     : 0
% 2.85/1.42  #Sup     : 157
% 2.85/1.42  #Fact    : 0
% 2.85/1.42  #Define  : 0
% 2.85/1.42  #Split   : 2
% 2.85/1.42  #Chain   : 0
% 2.85/1.42  #Close   : 0
% 2.85/1.42  
% 2.85/1.42  Ordering : KBO
% 2.85/1.42  
% 2.85/1.42  Simplification rules
% 2.85/1.42  ----------------------
% 2.85/1.42  #Subsume      : 28
% 2.85/1.42  #Demod        : 29
% 2.85/1.42  #Tautology    : 58
% 2.85/1.42  #SimpNegUnit  : 6
% 2.85/1.42  #BackRed      : 1
% 2.85/1.42  
% 2.85/1.42  #Partial instantiations: 0
% 2.85/1.42  #Strategies tried      : 1
% 2.85/1.42  
% 2.85/1.42  Timing (in seconds)
% 2.85/1.42  ----------------------
% 2.85/1.42  Preprocessing        : 0.32
% 2.85/1.42  Parsing              : 0.17
% 2.85/1.42  CNF conversion       : 0.02
% 2.85/1.42  Main loop            : 0.31
% 2.85/1.42  Inferencing          : 0.12
% 2.85/1.42  Reduction            : 0.09
% 2.85/1.42  Demodulation         : 0.06
% 2.85/1.42  BG Simplification    : 0.02
% 2.85/1.42  Subsumption          : 0.06
% 2.85/1.42  Abstraction          : 0.02
% 2.85/1.42  MUC search           : 0.00
% 2.85/1.42  Cooper               : 0.00
% 2.85/1.42  Total                : 0.66
% 2.85/1.42  Index Insertion      : 0.00
% 2.85/1.42  Index Deletion       : 0.00
% 2.85/1.42  Index Matching       : 0.00
% 2.85/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
