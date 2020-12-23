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
% DateTime   : Thu Dec  3 10:31:31 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 109 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 289 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_44,axiom,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_90,axiom,(
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

tff(f_111,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_54,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_74,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_74])).

tff(c_79,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_77])).

tff(c_80,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_79])).

tff(c_38,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),B_36)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(k1_tarski(A_35),B_36) = k1_tarski(A_35)
      | r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_69,c_12])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_115,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | k4_xboole_0(A_54,B_53) != A_54 ) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_236,plain,(
    ! [A_74,B_75,A_76] :
      ( ~ r2_hidden('#skF_1'(A_74,B_75),A_76)
      | k4_xboole_0(A_76,A_74) != A_76
      | r1_xboole_0(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_256,plain,(
    ! [B_80,A_81] :
      ( k4_xboole_0(B_80,A_81) != B_80
      | r1_xboole_0(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_236])).

tff(c_273,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = A_84
      | k4_xboole_0(B_85,A_84) != B_85 ) ),
    inference(resolution,[status(thm)],[c_256,c_12])).

tff(c_326,plain,(
    ! [B_91,A_92] :
      ( k4_xboole_0(B_91,k1_tarski(A_92)) = B_91
      | r2_hidden(A_92,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_273])).

tff(c_122,plain,(
    ! [A_55,B_56,C_57] :
      ( k7_subset_1(A_55,B_56,C_57) = k4_xboole_0(B_56,C_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    ! [C_57] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',C_57) = k4_xboole_0('#skF_3',C_57) ),
    inference(resolution,[status(thm)],[c_32,c_122])).

tff(c_175,plain,(
    ! [A_67,B_68] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67))),B_68,k1_tarski(k1_xboole_0)) = k2_yellow19(A_67,k3_yellow19(A_67,k2_struct_0(A_67),B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67)))))
      | ~ v13_waybel_0(B_68,k3_yellow_1(k2_struct_0(A_67)))
      | ~ v2_waybel_0(B_68,k3_yellow_1(k2_struct_0(A_67)))
      | v1_xboole_0(B_68)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_177,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_175])).

tff(c_180,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_125,c_177])).

tff(c_181,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_180])).

tff(c_30,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_215,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_30])).

tff(c_358,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_215])).

tff(c_28,plain,(
    ! [C_27,B_25,A_21] :
      ( ~ v1_xboole_0(C_27)
      | ~ r2_hidden(C_27,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21))))
      | ~ v13_waybel_0(B_25,k3_yellow_1(A_21))
      | ~ v2_waybel_0(B_25,k3_yellow_1(A_21))
      | ~ v1_subset_1(B_25,u1_struct_0(k3_yellow_1(A_21)))
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_367,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_21)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_358,c_28])).

tff(c_375,plain,(
    ! [A_21] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_21)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_439,plain,(
    ! [A_99] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_99))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_99))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_99))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_99)))
      | v1_xboole_0(A_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_375])).

tff(c_442,plain,
    ( ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_439])).

tff(c_445,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_442])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:40:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.37  
% 2.69/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.37  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.69/1.37  
% 2.69/1.37  %Foreground sorts:
% 2.69/1.37  
% 2.69/1.37  
% 2.69/1.37  %Background operators:
% 2.69/1.37  
% 2.69/1.37  
% 2.69/1.37  %Foreground operators:
% 2.69/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.69/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.37  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.69/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.37  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.69/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.37  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.69/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.37  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.69/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.37  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.69/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.37  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.69/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.69/1.37  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.69/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.37  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.69/1.37  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.69/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.69/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.37  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.69/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.37  
% 2.69/1.39  tff(f_131, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.69/1.39  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.69/1.39  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.69/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.39  tff(f_55, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.69/1.39  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.69/1.39  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.69/1.39  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.69/1.39  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.69/1.39  tff(f_111, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.69/1.39  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_42, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_54, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.39  tff(c_58, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.69/1.39  tff(c_74, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.69/1.39  tff(c_77, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_74])).
% 2.69/1.39  tff(c_79, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_77])).
% 2.69/1.39  tff(c_80, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_79])).
% 2.69/1.39  tff(c_38, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_36, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_34, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.69/1.39  tff(c_69, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), B_36) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.39  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.39  tff(c_73, plain, (![A_35, B_36]: (k4_xboole_0(k1_tarski(A_35), B_36)=k1_tarski(A_35) | r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_69, c_12])).
% 2.69/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.39  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.39  tff(c_14, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.39  tff(c_92, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, B_45) | ~r2_hidden(C_46, A_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.39  tff(c_115, plain, (![C_52, B_53, A_54]: (~r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | k4_xboole_0(A_54, B_53)!=A_54)), inference(resolution, [status(thm)], [c_14, c_92])).
% 2.69/1.39  tff(c_236, plain, (![A_74, B_75, A_76]: (~r2_hidden('#skF_1'(A_74, B_75), A_76) | k4_xboole_0(A_76, A_74)!=A_76 | r1_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_8, c_115])).
% 2.69/1.39  tff(c_256, plain, (![B_80, A_81]: (k4_xboole_0(B_80, A_81)!=B_80 | r1_xboole_0(A_81, B_80))), inference(resolution, [status(thm)], [c_6, c_236])).
% 2.69/1.39  tff(c_273, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=A_84 | k4_xboole_0(B_85, A_84)!=B_85)), inference(resolution, [status(thm)], [c_256, c_12])).
% 2.69/1.39  tff(c_326, plain, (![B_91, A_92]: (k4_xboole_0(B_91, k1_tarski(A_92))=B_91 | r2_hidden(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_73, c_273])).
% 2.69/1.39  tff(c_122, plain, (![A_55, B_56, C_57]: (k7_subset_1(A_55, B_56, C_57)=k4_xboole_0(B_56, C_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.39  tff(c_125, plain, (![C_57]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', C_57)=k4_xboole_0('#skF_3', C_57))), inference(resolution, [status(thm)], [c_32, c_122])).
% 2.69/1.39  tff(c_175, plain, (![A_67, B_68]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67))), B_68, k1_tarski(k1_xboole_0))=k2_yellow19(A_67, k3_yellow19(A_67, k2_struct_0(A_67), B_68)) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67))))) | ~v13_waybel_0(B_68, k3_yellow_1(k2_struct_0(A_67))) | ~v2_waybel_0(B_68, k3_yellow_1(k2_struct_0(A_67))) | v1_xboole_0(B_68) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.69/1.39  tff(c_177, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_175])).
% 2.69/1.39  tff(c_180, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_125, c_177])).
% 2.69/1.39  tff(c_181, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_180])).
% 2.69/1.39  tff(c_30, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.69/1.39  tff(c_215, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_30])).
% 2.69/1.39  tff(c_358, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_215])).
% 2.69/1.39  tff(c_28, plain, (![C_27, B_25, A_21]: (~v1_xboole_0(C_27) | ~r2_hidden(C_27, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21)))) | ~v13_waybel_0(B_25, k3_yellow_1(A_21)) | ~v2_waybel_0(B_25, k3_yellow_1(A_21)) | ~v1_subset_1(B_25, u1_struct_0(k3_yellow_1(A_21))) | v1_xboole_0(B_25) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.69/1.39  tff(c_367, plain, (![A_21]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_21))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_358, c_28])).
% 2.69/1.39  tff(c_375, plain, (![A_21]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_21))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_367])).
% 2.69/1.39  tff(c_439, plain, (![A_99]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_99)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_99)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_99)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_99))) | v1_xboole_0(A_99))), inference(negUnitSimplification, [status(thm)], [c_40, c_375])).
% 2.69/1.39  tff(c_442, plain, (~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_439])).
% 2.69/1.39  tff(c_445, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_442])).
% 2.69/1.39  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_445])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 94
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 0
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 16
% 2.69/1.39  #Demod        : 13
% 2.69/1.39  #Tautology    : 26
% 2.69/1.39  #SimpNegUnit  : 4
% 2.69/1.39  #BackRed      : 1
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 2.69/1.39  Preprocessing        : 0.35
% 2.69/1.39  Parsing              : 0.18
% 2.69/1.39  CNF conversion       : 0.02
% 2.69/1.39  Main loop            : 0.26
% 2.69/1.39  Inferencing          : 0.10
% 2.69/1.39  Reduction            : 0.07
% 2.69/1.39  Demodulation         : 0.05
% 2.69/1.39  BG Simplification    : 0.02
% 2.69/1.39  Subsumption          : 0.05
% 2.69/1.39  Abstraction          : 0.02
% 2.69/1.39  MUC search           : 0.00
% 2.69/1.39  Cooper               : 0.00
% 2.69/1.39  Total                : 0.65
% 2.69/1.39  Index Insertion      : 0.00
% 2.69/1.39  Index Deletion       : 0.00
% 2.69/1.39  Index Matching       : 0.00
% 2.69/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
