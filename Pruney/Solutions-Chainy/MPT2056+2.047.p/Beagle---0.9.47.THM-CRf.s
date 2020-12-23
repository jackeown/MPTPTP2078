%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:31 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 208 expanded)
%              Number of leaves         :   39 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 649 expanded)
%              Number of equality atoms :   21 ( 109 expanded)
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

tff(f_132,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_112,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_160,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_subset_1(A_61,B_62,C_63) = k4_xboole_0(B_62,C_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_163,plain,(
    ! [C_63] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',C_63) = k4_xboole_0('#skF_3',C_63) ),
    inference(resolution,[status(thm)],[c_32,c_160])).

tff(c_298,plain,(
    ! [A_82,B_83] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_82))),B_83,k1_tarski(k1_xboole_0)) = k2_yellow19(A_82,k3_yellow19(A_82,k2_struct_0(A_82),B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_82)))))
      | ~ v13_waybel_0(B_83,k3_yellow_1(k2_struct_0(A_82)))
      | ~ v2_waybel_0(B_83,k3_yellow_1(k2_struct_0(A_82)))
      | v1_xboole_0(B_83)
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_300,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_298])).

tff(c_303,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_163,c_300])).

tff(c_304,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_303])).

tff(c_30,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_312,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_30])).

tff(c_92,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),k1_tarski(B_36))
      | B_36 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden(A_10,B_11)
      | ~ r1_xboole_0(k1_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,k1_tarski(B_36))
      | B_36 = A_35 ) ),
    inference(resolution,[status(thm)],[c_61,c_16])).

tff(c_120,plain,(
    ! [A_55,B_56] :
      ( '#skF_1'(A_55,k1_tarski(B_56)) = B_56
      | r1_xboole_0(A_55,k1_tarski(B_56)) ) ),
    inference(resolution,[status(thm)],[c_92,c_65])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,k1_tarski(B_56)) = A_55
      | '#skF_1'(A_55,k1_tarski(B_56)) = B_56 ) ),
    inference(resolution,[status(thm)],[c_120,c_12])).

tff(c_320,plain,(
    '#skF_1'('#skF_3',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_312])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_327,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_8])).

tff(c_331,plain,(
    r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_336,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_331,c_12])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_336])).

tff(c_343,plain,(
    ~ r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_189,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ v1_xboole_0(C_71)
      | ~ r2_hidden(C_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_73))))
      | ~ v13_waybel_0(B_72,k3_yellow_1(A_73))
      | ~ v2_waybel_0(B_72,k3_yellow_1(A_73))
      | ~ v1_subset_1(B_72,u1_struct_0(k3_yellow_1(A_73)))
      | v1_xboole_0(B_72)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_385,plain,(
    ! [A_86,B_87,A_88] :
      ( ~ v1_xboole_0('#skF_1'(A_86,B_87))
      | ~ m1_subset_1(A_86,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_88))))
      | ~ v13_waybel_0(A_86,k3_yellow_1(A_88))
      | ~ v2_waybel_0(A_86,k3_yellow_1(A_88))
      | ~ v1_subset_1(A_86,u1_struct_0(k3_yellow_1(A_88)))
      | v1_xboole_0(A_86)
      | v1_xboole_0(A_88)
      | r1_xboole_0(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_8,c_189])).

tff(c_387,plain,(
    ! [A_88] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_88))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_88))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_88))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_88)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_88)
      | r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_385])).

tff(c_393,plain,(
    ! [A_88] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_88))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_88))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_88))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_88)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_88)
      | r1_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_387])).

tff(c_408,plain,(
    ! [A_90] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_90))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_90))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_90))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_90)))
      | v1_xboole_0(A_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_40,c_393])).

tff(c_411,plain,
    ( ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_408])).

tff(c_414,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_411])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k2_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_417,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_414,c_22])).

tff(c_420,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_417])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.39  
% 2.40/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.39  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.39  
% 2.40/1.39  %Foreground sorts:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Background operators:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Foreground operators:
% 2.40/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.39  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.40/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.40/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.39  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.40/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.39  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.40/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.40/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.40/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.39  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.40/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.39  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.40/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.40/1.39  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.39  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.40/1.39  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.40/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.40/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.39  
% 2.72/1.41  tff(f_132, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.72/1.41  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.72/1.41  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.72/1.41  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.72/1.41  tff(f_60, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.72/1.41  tff(f_55, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.72/1.41  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.72/1.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.72/1.41  tff(f_112, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.72/1.41  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.72/1.41  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_42, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_38, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_36, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_34, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_160, plain, (![A_61, B_62, C_63]: (k7_subset_1(A_61, B_62, C_63)=k4_xboole_0(B_62, C_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.41  tff(c_163, plain, (![C_63]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', C_63)=k4_xboole_0('#skF_3', C_63))), inference(resolution, [status(thm)], [c_32, c_160])).
% 2.72/1.41  tff(c_298, plain, (![A_82, B_83]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_82))), B_83, k1_tarski(k1_xboole_0))=k2_yellow19(A_82, k3_yellow19(A_82, k2_struct_0(A_82), B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_82))))) | ~v13_waybel_0(B_83, k3_yellow_1(k2_struct_0(A_82))) | ~v2_waybel_0(B_83, k3_yellow_1(k2_struct_0(A_82))) | v1_xboole_0(B_83) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.41  tff(c_300, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_298])).
% 2.72/1.41  tff(c_303, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_163, c_300])).
% 2.72/1.41  tff(c_304, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_303])).
% 2.72/1.41  tff(c_30, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.72/1.41  tff(c_312, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_30])).
% 2.72/1.41  tff(c_92, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), B_47) | r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.41  tff(c_61, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), k1_tarski(B_36)) | B_36=A_35)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.41  tff(c_16, plain, (![A_10, B_11]: (~r2_hidden(A_10, B_11) | ~r1_xboole_0(k1_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.41  tff(c_65, plain, (![A_35, B_36]: (~r2_hidden(A_35, k1_tarski(B_36)) | B_36=A_35)), inference(resolution, [status(thm)], [c_61, c_16])).
% 2.72/1.41  tff(c_120, plain, (![A_55, B_56]: ('#skF_1'(A_55, k1_tarski(B_56))=B_56 | r1_xboole_0(A_55, k1_tarski(B_56)))), inference(resolution, [status(thm)], [c_92, c_65])).
% 2.72/1.41  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.41  tff(c_131, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k1_tarski(B_56))=A_55 | '#skF_1'(A_55, k1_tarski(B_56))=B_56)), inference(resolution, [status(thm)], [c_120, c_12])).
% 2.72/1.41  tff(c_320, plain, ('#skF_1'('#skF_3', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_131, c_312])).
% 2.72/1.41  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.41  tff(c_327, plain, (r2_hidden(k1_xboole_0, '#skF_3') | r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_320, c_8])).
% 2.72/1.41  tff(c_331, plain, (r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_327])).
% 2.72/1.41  tff(c_336, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))='#skF_3'), inference(resolution, [status(thm)], [c_331, c_12])).
% 2.72/1.41  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_336])).
% 2.72/1.41  tff(c_343, plain, (~r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_327])).
% 2.72/1.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.72/1.41  tff(c_189, plain, (![C_71, B_72, A_73]: (~v1_xboole_0(C_71) | ~r2_hidden(C_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_73)))) | ~v13_waybel_0(B_72, k3_yellow_1(A_73)) | ~v2_waybel_0(B_72, k3_yellow_1(A_73)) | ~v1_subset_1(B_72, u1_struct_0(k3_yellow_1(A_73))) | v1_xboole_0(B_72) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.72/1.41  tff(c_385, plain, (![A_86, B_87, A_88]: (~v1_xboole_0('#skF_1'(A_86, B_87)) | ~m1_subset_1(A_86, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_88)))) | ~v13_waybel_0(A_86, k3_yellow_1(A_88)) | ~v2_waybel_0(A_86, k3_yellow_1(A_88)) | ~v1_subset_1(A_86, u1_struct_0(k3_yellow_1(A_88))) | v1_xboole_0(A_86) | v1_xboole_0(A_88) | r1_xboole_0(A_86, B_87))), inference(resolution, [status(thm)], [c_8, c_189])).
% 2.72/1.41  tff(c_387, plain, (![A_88]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_88)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_88)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_88)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_88))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_88) | r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_320, c_385])).
% 2.72/1.41  tff(c_393, plain, (![A_88]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_88)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_88)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_88)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_88))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_88) | r1_xboole_0('#skF_3', k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_387])).
% 2.72/1.41  tff(c_408, plain, (![A_90]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_90)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_90)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_90)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_90))) | v1_xboole_0(A_90))), inference(negUnitSimplification, [status(thm)], [c_343, c_40, c_393])).
% 2.72/1.41  tff(c_411, plain, (~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_408])).
% 2.72/1.41  tff(c_414, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_411])).
% 2.72/1.41  tff(c_22, plain, (![A_17]: (~v1_xboole_0(k2_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.72/1.41  tff(c_417, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_414, c_22])).
% 2.72/1.41  tff(c_420, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_417])).
% 2.72/1.41  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_420])).
% 2.72/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  Inference rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Ref     : 0
% 2.72/1.41  #Sup     : 89
% 2.72/1.41  #Fact    : 0
% 2.72/1.41  #Define  : 0
% 2.72/1.41  #Split   : 1
% 2.72/1.41  #Chain   : 0
% 2.72/1.41  #Close   : 0
% 2.72/1.41  
% 2.72/1.41  Ordering : KBO
% 2.72/1.41  
% 2.72/1.41  Simplification rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Subsume      : 11
% 2.72/1.41  #Demod        : 14
% 2.72/1.41  #Tautology    : 30
% 2.72/1.41  #SimpNegUnit  : 5
% 2.72/1.41  #BackRed      : 1
% 2.72/1.41  
% 2.72/1.41  #Partial instantiations: 0
% 2.72/1.41  #Strategies tried      : 1
% 2.72/1.41  
% 2.72/1.41  Timing (in seconds)
% 2.72/1.41  ----------------------
% 2.72/1.41  Preprocessing        : 0.35
% 2.72/1.41  Parsing              : 0.18
% 2.72/1.41  CNF conversion       : 0.02
% 2.72/1.41  Main loop            : 0.26
% 2.72/1.41  Inferencing          : 0.10
% 2.72/1.41  Reduction            : 0.07
% 2.72/1.41  Demodulation         : 0.05
% 2.72/1.41  BG Simplification    : 0.02
% 2.72/1.41  Subsumption          : 0.05
% 2.72/1.41  Abstraction          : 0.02
% 2.72/1.41  MUC search           : 0.00
% 2.72/1.41  Cooper               : 0.00
% 2.72/1.41  Total                : 0.64
% 2.72/1.41  Index Insertion      : 0.00
% 2.72/1.41  Index Deletion       : 0.00
% 2.72/1.41  Index Matching       : 0.00
% 2.72/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
