%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:32 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   72 (  95 expanded)
%              Number of leaves         :   36 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 260 expanded)
%              Number of equality atoms :   14 (  28 expanded)
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

tff(f_125,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_105,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

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
      ( r1_xboole_0(k1_tarski(A_8),B_9)
      | r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,B_39)
      | ~ r2_hidden(C_40,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,k1_tarski(A_45))
      | r2_hidden(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_14,c_64])).

tff(c_202,plain,(
    ! [A_68,B_69,A_70] :
      ( ~ r2_hidden('#skF_1'(A_68,B_69),k1_tarski(A_70))
      | r2_hidden(A_70,A_68)
      | r1_xboole_0(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_230,plain,(
    ! [A_73,A_74] :
      ( r2_hidden(A_73,A_74)
      | r1_xboole_0(A_74,k1_tarski(A_73)) ) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_237,plain,(
    ! [A_74,A_73] :
      ( k4_xboole_0(A_74,k1_tarski(A_73)) = A_74
      | r2_hidden(A_73,A_74) ) ),
    inference(resolution,[status(thm)],[c_230,c_10])).

tff(c_87,plain,(
    ! [A_46,B_47,C_48] :
      ( k7_subset_1(A_46,B_47,C_48) = k4_xboole_0(B_47,C_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,(
    ! [C_48] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',C_48) = k4_xboole_0('#skF_3',C_48) ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_223,plain,(
    ! [A_71,B_72] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_71))),B_72,k1_tarski(k1_xboole_0)) = k2_yellow19(A_71,k3_yellow19(A_71,k2_struct_0(A_71),B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_71)))))
      | ~ v13_waybel_0(B_72,k3_yellow_1(k2_struct_0(A_71)))
      | ~ v2_waybel_0(B_72,k3_yellow_1(k2_struct_0(A_71)))
      | v1_xboole_0(B_72)
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_225,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_228,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_90,c_225])).

tff(c_229,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_228])).

tff(c_26,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_380,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_26])).

tff(c_389,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_380])).

tff(c_24,plain,(
    ! [C_24,B_22,A_18] :
      ( ~ v1_xboole_0(C_24)
      | ~ r2_hidden(C_24,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18))))
      | ~ v13_waybel_0(B_22,k3_yellow_1(A_18))
      | ~ v2_waybel_0(B_22,k3_yellow_1(A_18))
      | ~ v1_subset_1(B_22,u1_struct_0(k3_yellow_1(A_18)))
      | v1_xboole_0(B_22)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_391,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_18))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_18))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_18)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_389,c_24])).

tff(c_396,plain,(
    ! [A_18] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_18))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_18))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_18)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_391])).

tff(c_424,plain,(
    ! [A_85] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_85))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_85))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_85))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_85)))
      | v1_xboole_0(A_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_396])).

tff(c_427,plain,
    ( ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_424])).

tff(c_430,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_427])).

tff(c_18,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_433,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_430,c_18])).

tff(c_436,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_433])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.33  
% 2.48/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.33  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.33  
% 2.48/1.33  %Foreground sorts:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Background operators:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Foreground operators:
% 2.48/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.33  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.48/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.48/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.33  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.48/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.33  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.48/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.33  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.48/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.33  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.48/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.48/1.33  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.33  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.48/1.33  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.48/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.48/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.48/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.33  
% 2.48/1.35  tff(f_125, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.48/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.35  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.48/1.35  tff(f_53, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.48/1.35  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.48/1.35  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.48/1.35  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.48/1.35  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.48/1.35  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.48/1.35  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_38, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_34, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_32, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_30, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.48/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.48/1.35  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.48/1.35  tff(c_14, plain, (![A_8, B_9]: (r1_xboole_0(k1_tarski(A_8), B_9) | r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.35  tff(c_64, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, B_39) | ~r2_hidden(C_40, A_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.48/1.35  tff(c_80, plain, (![C_43, B_44, A_45]: (~r2_hidden(C_43, B_44) | ~r2_hidden(C_43, k1_tarski(A_45)) | r2_hidden(A_45, B_44))), inference(resolution, [status(thm)], [c_14, c_64])).
% 2.48/1.35  tff(c_202, plain, (![A_68, B_69, A_70]: (~r2_hidden('#skF_1'(A_68, B_69), k1_tarski(A_70)) | r2_hidden(A_70, A_68) | r1_xboole_0(A_68, B_69))), inference(resolution, [status(thm)], [c_8, c_80])).
% 2.48/1.35  tff(c_230, plain, (![A_73, A_74]: (r2_hidden(A_73, A_74) | r1_xboole_0(A_74, k1_tarski(A_73)))), inference(resolution, [status(thm)], [c_6, c_202])).
% 2.48/1.35  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.35  tff(c_237, plain, (![A_74, A_73]: (k4_xboole_0(A_74, k1_tarski(A_73))=A_74 | r2_hidden(A_73, A_74))), inference(resolution, [status(thm)], [c_230, c_10])).
% 2.48/1.35  tff(c_87, plain, (![A_46, B_47, C_48]: (k7_subset_1(A_46, B_47, C_48)=k4_xboole_0(B_47, C_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.35  tff(c_90, plain, (![C_48]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', C_48)=k4_xboole_0('#skF_3', C_48))), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.48/1.35  tff(c_223, plain, (![A_71, B_72]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_71))), B_72, k1_tarski(k1_xboole_0))=k2_yellow19(A_71, k3_yellow19(A_71, k2_struct_0(A_71), B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_71))))) | ~v13_waybel_0(B_72, k3_yellow_1(k2_struct_0(A_71))) | ~v2_waybel_0(B_72, k3_yellow_1(k2_struct_0(A_71))) | v1_xboole_0(B_72) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.48/1.35  tff(c_225, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_223])).
% 2.48/1.35  tff(c_228, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_90, c_225])).
% 2.48/1.35  tff(c_229, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_228])).
% 2.48/1.35  tff(c_26, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.48/1.35  tff(c_380, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_26])).
% 2.48/1.35  tff(c_389, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_237, c_380])).
% 2.48/1.35  tff(c_24, plain, (![C_24, B_22, A_18]: (~v1_xboole_0(C_24) | ~r2_hidden(C_24, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18)))) | ~v13_waybel_0(B_22, k3_yellow_1(A_18)) | ~v2_waybel_0(B_22, k3_yellow_1(A_18)) | ~v1_subset_1(B_22, u1_struct_0(k3_yellow_1(A_18))) | v1_xboole_0(B_22) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.48/1.35  tff(c_391, plain, (![A_18]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_18)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_18)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_18))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_389, c_24])).
% 2.48/1.35  tff(c_396, plain, (![A_18]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_18)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_18)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_18))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_391])).
% 2.48/1.35  tff(c_424, plain, (![A_85]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_85)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_85)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_85)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_85))) | v1_xboole_0(A_85))), inference(negUnitSimplification, [status(thm)], [c_36, c_396])).
% 2.48/1.35  tff(c_427, plain, (~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_424])).
% 2.48/1.35  tff(c_430, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_427])).
% 2.48/1.35  tff(c_18, plain, (![A_13]: (~v1_xboole_0(k2_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.35  tff(c_433, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_430, c_18])).
% 2.48/1.35  tff(c_436, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_433])).
% 2.48/1.35  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_436])).
% 2.48/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  Inference rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Ref     : 0
% 2.48/1.35  #Sup     : 93
% 2.48/1.35  #Fact    : 0
% 2.48/1.35  #Define  : 0
% 2.48/1.35  #Split   : 0
% 2.48/1.35  #Chain   : 0
% 2.48/1.35  #Close   : 0
% 2.48/1.35  
% 2.48/1.35  Ordering : KBO
% 2.48/1.35  
% 2.48/1.35  Simplification rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Subsume      : 15
% 2.48/1.35  #Demod        : 10
% 2.48/1.35  #Tautology    : 31
% 2.48/1.35  #SimpNegUnit  : 3
% 2.48/1.35  #BackRed      : 1
% 2.48/1.35  
% 2.48/1.35  #Partial instantiations: 0
% 2.48/1.35  #Strategies tried      : 1
% 2.48/1.35  
% 2.48/1.35  Timing (in seconds)
% 2.48/1.35  ----------------------
% 2.48/1.35  Preprocessing        : 0.32
% 2.48/1.35  Parsing              : 0.18
% 2.48/1.35  CNF conversion       : 0.02
% 2.48/1.35  Main loop            : 0.24
% 2.48/1.35  Inferencing          : 0.10
% 2.48/1.35  Reduction            : 0.06
% 2.48/1.35  Demodulation         : 0.05
% 2.48/1.35  BG Simplification    : 0.02
% 2.48/1.35  Subsumption          : 0.05
% 2.48/1.35  Abstraction          : 0.02
% 2.48/1.35  MUC search           : 0.00
% 2.48/1.35  Cooper               : 0.00
% 2.48/1.35  Total                : 0.60
% 2.48/1.35  Index Insertion      : 0.00
% 2.48/1.35  Index Deletion       : 0.00
% 2.48/1.35  Index Matching       : 0.00
% 2.48/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
