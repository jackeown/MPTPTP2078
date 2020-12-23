%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:30 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 172 expanded)
%              Number of leaves         :   38 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 519 expanded)
%              Number of equality atoms :   24 (  86 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_134,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_93,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_114,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_84,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_87,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_84])).

tff(c_89,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_90,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_89])).

tff(c_38,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_139,plain,(
    ! [A_55,B_56,C_57] :
      ( k7_subset_1(A_55,B_56,C_57) = k4_xboole_0(B_56,C_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_142,plain,(
    ! [C_57] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',C_57) = k4_xboole_0('#skF_3',C_57) ),
    inference(resolution,[status(thm)],[c_32,c_139])).

tff(c_341,plain,(
    ! [A_84,B_85] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_84))),B_85,k1_tarski(k1_xboole_0)) = k2_yellow19(A_84,k3_yellow19(A_84,k2_struct_0(A_84),B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_84)))))
      | ~ v13_waybel_0(B_85,k3_yellow_1(k2_struct_0(A_84)))
      | ~ v2_waybel_0(B_85,k3_yellow_1(k2_struct_0(A_84)))
      | v1_xboole_0(B_85)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_343,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_341])).

tff(c_346,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_142,c_343])).

tff(c_347,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_346])).

tff(c_30,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_348,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_30])).

tff(c_98,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),k1_tarski(B_38))
      | B_38 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden(A_8,B_9)
      | ~ r1_xboole_0(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,k1_tarski(B_38))
      | B_38 = A_37 ) ),
    inference(resolution,[status(thm)],[c_75,c_14])).

tff(c_126,plain,(
    ! [A_53,B_54] :
      ( '#skF_1'(A_53,k1_tarski(B_54)) = B_54
      | r1_xboole_0(A_53,k1_tarski(B_54)) ) ),
    inference(resolution,[status(thm)],[c_98,c_83])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_137,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,k1_tarski(B_54)) = A_53
      | '#skF_1'(A_53,k1_tarski(B_54)) = B_54 ) ),
    inference(resolution,[status(thm)],[c_126,c_10])).

tff(c_356,plain,(
    '#skF_1'('#skF_3',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_348])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_369,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_8])).

tff(c_375,plain,(
    r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_380,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_375,c_10])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_380])).

tff(c_386,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_369])).

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
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_400,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_21)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_386,c_28])).

tff(c_406,plain,(
    ! [A_21] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_21))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_21)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_400])).

tff(c_438,plain,(
    ! [A_89] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_89))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_89))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_89))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_89)))
      | v1_xboole_0(A_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_406])).

tff(c_441,plain,
    ( ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_438])).

tff(c_444,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_441])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:40:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.37  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.37  
% 2.51/1.37  %Foreground sorts:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Background operators:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Foreground operators:
% 2.51/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.37  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.51/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.37  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.51/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.37  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.51/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.37  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.51/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.51/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.37  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.51/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.37  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.51/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.51/1.37  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.37  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.51/1.37  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.51/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.37  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.51/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.37  
% 2.74/1.39  tff(f_134, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.74/1.39  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.74/1.39  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.74/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.74/1.39  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.74/1.39  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.74/1.39  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.74/1.39  tff(f_58, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.74/1.39  tff(f_53, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.74/1.39  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.74/1.39  tff(f_114, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.74/1.39  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_42, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_54, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.74/1.39  tff(c_58, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.74/1.39  tff(c_84, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.39  tff(c_87, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_84])).
% 2.74/1.39  tff(c_89, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_87])).
% 2.74/1.39  tff(c_90, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_89])).
% 2.74/1.39  tff(c_38, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_36, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_34, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.74/1.39  tff(c_139, plain, (![A_55, B_56, C_57]: (k7_subset_1(A_55, B_56, C_57)=k4_xboole_0(B_56, C_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.39  tff(c_142, plain, (![C_57]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', C_57)=k4_xboole_0('#skF_3', C_57))), inference(resolution, [status(thm)], [c_32, c_139])).
% 2.74/1.39  tff(c_341, plain, (![A_84, B_85]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_84))), B_85, k1_tarski(k1_xboole_0))=k2_yellow19(A_84, k3_yellow19(A_84, k2_struct_0(A_84), B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_84))))) | ~v13_waybel_0(B_85, k3_yellow_1(k2_struct_0(A_84))) | ~v2_waybel_0(B_85, k3_yellow_1(k2_struct_0(A_84))) | v1_xboole_0(B_85) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.39  tff(c_343, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_341])).
% 2.74/1.39  tff(c_346, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_142, c_343])).
% 2.74/1.39  tff(c_347, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_346])).
% 2.74/1.39  tff(c_30, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.74/1.39  tff(c_348, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_30])).
% 2.74/1.39  tff(c_98, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.39  tff(c_75, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), k1_tarski(B_38)) | B_38=A_37)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.39  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden(A_8, B_9) | ~r1_xboole_0(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.39  tff(c_83, plain, (![A_37, B_38]: (~r2_hidden(A_37, k1_tarski(B_38)) | B_38=A_37)), inference(resolution, [status(thm)], [c_75, c_14])).
% 2.74/1.39  tff(c_126, plain, (![A_53, B_54]: ('#skF_1'(A_53, k1_tarski(B_54))=B_54 | r1_xboole_0(A_53, k1_tarski(B_54)))), inference(resolution, [status(thm)], [c_98, c_83])).
% 2.74/1.39  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.74/1.39  tff(c_137, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k1_tarski(B_54))=A_53 | '#skF_1'(A_53, k1_tarski(B_54))=B_54)), inference(resolution, [status(thm)], [c_126, c_10])).
% 2.74/1.39  tff(c_356, plain, ('#skF_1'('#skF_3', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_137, c_348])).
% 2.74/1.39  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.39  tff(c_369, plain, (r2_hidden(k1_xboole_0, '#skF_3') | r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_356, c_8])).
% 2.74/1.39  tff(c_375, plain, (r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_369])).
% 2.74/1.39  tff(c_380, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))='#skF_3'), inference(resolution, [status(thm)], [c_375, c_10])).
% 2.74/1.39  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_380])).
% 2.74/1.39  tff(c_386, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(splitRight, [status(thm)], [c_369])).
% 2.74/1.39  tff(c_28, plain, (![C_27, B_25, A_21]: (~v1_xboole_0(C_27) | ~r2_hidden(C_27, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21)))) | ~v13_waybel_0(B_25, k3_yellow_1(A_21)) | ~v2_waybel_0(B_25, k3_yellow_1(A_21)) | ~v1_subset_1(B_25, u1_struct_0(k3_yellow_1(A_21))) | v1_xboole_0(B_25) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.74/1.39  tff(c_400, plain, (![A_21]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_21))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_386, c_28])).
% 2.74/1.39  tff(c_406, plain, (![A_21]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_21)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_21)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_21))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_400])).
% 2.74/1.39  tff(c_438, plain, (![A_89]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_89)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_89)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_89)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_89))) | v1_xboole_0(A_89))), inference(negUnitSimplification, [status(thm)], [c_40, c_406])).
% 2.74/1.39  tff(c_441, plain, (~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_438])).
% 2.74/1.39  tff(c_444, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_441])).
% 2.74/1.39  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_444])).
% 2.74/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  Inference rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Ref     : 0
% 2.74/1.39  #Sup     : 98
% 2.74/1.39  #Fact    : 0
% 2.74/1.39  #Define  : 0
% 2.74/1.39  #Split   : 1
% 2.74/1.39  #Chain   : 0
% 2.74/1.39  #Close   : 0
% 2.74/1.39  
% 2.74/1.39  Ordering : KBO
% 2.74/1.39  
% 2.74/1.39  Simplification rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Subsume      : 17
% 2.74/1.39  #Demod        : 16
% 2.74/1.39  #Tautology    : 31
% 2.74/1.39  #SimpNegUnit  : 5
% 2.74/1.39  #BackRed      : 1
% 2.74/1.39  
% 2.74/1.39  #Partial instantiations: 0
% 2.74/1.39  #Strategies tried      : 1
% 2.74/1.39  
% 2.74/1.39  Timing (in seconds)
% 2.74/1.39  ----------------------
% 2.74/1.39  Preprocessing        : 0.33
% 2.74/1.39  Parsing              : 0.18
% 2.74/1.39  CNF conversion       : 0.02
% 2.74/1.39  Main loop            : 0.25
% 2.74/1.39  Inferencing          : 0.10
% 2.74/1.39  Reduction            : 0.07
% 2.74/1.39  Demodulation         : 0.05
% 2.74/1.39  BG Simplification    : 0.02
% 2.74/1.39  Subsumption          : 0.05
% 2.74/1.39  Abstraction          : 0.02
% 2.74/1.39  MUC search           : 0.00
% 2.74/1.39  Cooper               : 0.00
% 2.74/1.39  Total                : 0.61
% 2.74/1.39  Index Insertion      : 0.00
% 2.74/1.39  Index Deletion       : 0.00
% 2.74/1.39  Index Matching       : 0.00
% 2.74/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
