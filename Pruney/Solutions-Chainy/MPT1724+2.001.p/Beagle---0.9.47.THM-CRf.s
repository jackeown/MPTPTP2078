%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:45 EST 2020

% Result     : Theorem 6.40s
% Output     : CNFRefutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :  225 (1346 expanded)
%              Number of leaves         :   21 ( 523 expanded)
%              Depth                    :   24
%              Number of atoms          : 1062 (9719 expanded)
%              Number of equality atoms :  118 (1382 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_183,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( k2_tsep_1(A,C,k1_tsep_1(A,B,D)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                          & k2_tsep_1(A,C,k1_tsep_1(A,D,B)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tmap_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( ~ ( ( r1_tsep_1(B,C)
                          | r1_tsep_1(C,B) )
                        & ~ ( r1_tsep_1(D,C)
                            & r1_tsep_1(C,D) )
                        & ~ ( k2_tsep_1(A,k1_tsep_1(A,B,D),C) = k2_tsep_1(A,D,C)
                            & k2_tsep_1(A,C,k1_tsep_1(A,B,D)) = k2_tsep_1(A,C,D) ) )
                    & ~ ( ~ ( r1_tsep_1(B,C)
                            & r1_tsep_1(C,B) )
                        & ( r1_tsep_1(D,C)
                          | r1_tsep_1(C,D) )
                        & ~ ( k2_tsep_1(A,k1_tsep_1(A,B,D),C) = k2_tsep_1(A,B,C)
                            & k2_tsep_1(A,C,k1_tsep_1(A,B,D)) = k2_tsep_1(A,C,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tmap_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ( ( m1_pre_topc(B,C)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                   => m1_pre_topc(B,C) )
                  & ( m1_pre_topc(C,B)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                   => m1_pre_topc(C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_50,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_48,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_69,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [C_20,B_16,D_22,A_8] :
      ( r1_tsep_1(C_20,B_16)
      | ~ r1_tsep_1(C_20,D_22)
      | k2_tsep_1(A_8,C_20,k1_tsep_1(A_8,B_16,D_22)) = k2_tsep_1(A_8,C_20,B_16)
      | ~ m1_pre_topc(D_22,A_8)
      | v2_struct_0(D_22)
      | ~ m1_pre_topc(C_20,A_8)
      | v2_struct_0(C_20)
      | ~ m1_pre_topc(B_16,A_8)
      | v2_struct_0(B_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1138,plain,(
    ! [B_108,C_109,D_110,A_111] :
      ( r1_tsep_1(B_108,C_109)
      | ~ r1_tsep_1(D_110,C_109)
      | k2_tsep_1(A_111,C_109,k1_tsep_1(A_111,B_108,D_110)) = k2_tsep_1(A_111,C_109,B_108)
      | ~ m1_pre_topc(D_110,A_111)
      | v2_struct_0(D_110)
      | ~ m1_pre_topc(C_109,A_111)
      | v2_struct_0(C_109)
      | ~ m1_pre_topc(B_108,A_111)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_176,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tsep_1(A_54,B_55,C_56) = g1_pre_topc(u1_struct_0(B_55),u1_pre_topc(B_55))
      | ~ m1_pre_topc(B_55,C_56)
      | r1_tsep_1(B_55,C_56)
      | ~ m1_pre_topc(C_56,A_54)
      | v2_struct_0(C_56)
      | ~ m1_pre_topc(B_55,A_54)
      | v2_struct_0(B_55)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_184,plain,(
    ! [B_55] :
      ( g1_pre_topc(u1_struct_0(B_55),u1_pre_topc(B_55)) = k2_tsep_1('#skF_1',B_55,'#skF_3')
      | ~ m1_pre_topc(B_55,'#skF_3')
      | r1_tsep_1(B_55,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_55,'#skF_1')
      | v2_struct_0(B_55)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_176])).

tff(c_198,plain,(
    ! [B_55] :
      ( g1_pre_topc(u1_struct_0(B_55),u1_pre_topc(B_55)) = k2_tsep_1('#skF_1',B_55,'#skF_3')
      | ~ m1_pre_topc(B_55,'#skF_3')
      | r1_tsep_1(B_55,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_55,'#skF_1')
      | v2_struct_0(B_55)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_184])).

tff(c_310,plain,(
    ! [B_59] :
      ( g1_pre_topc(u1_struct_0(B_59),u1_pre_topc(B_59)) = k2_tsep_1('#skF_1',B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | r1_tsep_1(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_1')
      | v2_struct_0(B_59) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_198])).

tff(c_85,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_tsep_1(A_47,B_48,C_49) = g1_pre_topc(u1_struct_0(C_49),u1_pre_topc(C_49))
      | ~ m1_pre_topc(C_49,B_48)
      | r1_tsep_1(B_48,C_49)
      | ~ m1_pre_topc(C_49,A_47)
      | v2_struct_0(C_49)
      | ~ m1_pre_topc(B_48,A_47)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_89,plain,(
    ! [B_48] :
      ( k2_tsep_1('#skF_1',B_48,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_48)
      | r1_tsep_1(B_48,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_48,'#skF_1')
      | v2_struct_0(B_48)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_100,plain,(
    ! [B_48] :
      ( k2_tsep_1('#skF_1',B_48,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_48)
      | r1_tsep_1(B_48,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_48,'#skF_1')
      | v2_struct_0(B_48)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_89])).

tff(c_101,plain,(
    ! [B_48] :
      ( k2_tsep_1('#skF_1',B_48,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_48)
      | r1_tsep_1(B_48,'#skF_2')
      | ~ m1_pre_topc(B_48,'#skF_1')
      | v2_struct_0(B_48) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_100])).

tff(c_325,plain,(
    ! [B_48] :
      ( k2_tsep_1('#skF_1',B_48,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_48)
      | r1_tsep_1(B_48,'#skF_2')
      | ~ m1_pre_topc(B_48,'#skF_1')
      | v2_struct_0(B_48)
      | ~ m1_pre_topc('#skF_2','#skF_3')
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_101])).

tff(c_355,plain,(
    ! [B_48] :
      ( k2_tsep_1('#skF_1',B_48,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_48)
      | r1_tsep_1(B_48,'#skF_2')
      | ~ m1_pre_topc(B_48,'#skF_1')
      | v2_struct_0(B_48)
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_325])).

tff(c_356,plain,(
    ! [B_48] :
      ( k2_tsep_1('#skF_1',B_48,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_48)
      | r1_tsep_1(B_48,'#skF_2')
      | ~ m1_pre_topc(B_48,'#skF_1')
      | v2_struct_0(B_48)
      | r1_tsep_1('#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_355])).

tff(c_390,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_4,plain,(
    ! [B_5,C_7,A_1] :
      ( ~ r1_tsep_1(B_5,C_7)
      | ~ m1_pre_topc(B_5,C_7)
      | ~ m1_pre_topc(C_7,A_1)
      | v2_struct_0(C_7)
      | ~ m1_pre_topc(B_5,A_1)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_394,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_390,c_4])).

tff(c_400,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_394])).

tff(c_402,plain,(
    ! [A_63] :
      ( ~ m1_pre_topc('#skF_3',A_63)
      | ~ m1_pre_topc('#skF_2',A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_400])).

tff(c_405,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_402])).

tff(c_411,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_405])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_411])).

tff(c_415,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_533,plain,(
    ! [B_72,C_73,D_74,A_75] :
      ( r1_tsep_1(B_72,C_73)
      | ~ r1_tsep_1(C_73,D_74)
      | k2_tsep_1(A_75,C_73,k1_tsep_1(A_75,B_72,D_74)) = k2_tsep_1(A_75,C_73,B_72)
      | ~ m1_pre_topc(D_74,A_75)
      | v2_struct_0(D_74)
      | ~ m1_pre_topc(C_73,A_75)
      | v2_struct_0(C_73)
      | ~ m1_pre_topc(B_72,A_75)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2'))
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_84,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_331,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_84])).

tff(c_361,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_331])).

tff(c_362,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_361])).

tff(c_373,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_547,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_373])).

tff(c_560,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_52,c_69,c_547])).

tff(c_561,plain,(
    k2_tsep_1('#skF_1','#skF_2','#skF_3') != k2_tsep_1('#skF_1','#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_54,c_415,c_560])).

tff(c_422,plain,(
    ! [B_64] :
      ( k2_tsep_1('#skF_1',B_64,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_64)
      | r1_tsep_1(B_64,'#skF_2')
      | ~ m1_pre_topc(B_64,'#skF_1')
      | v2_struct_0(B_64) ) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_2,plain,(
    ! [C_7,B_5,A_1] :
      ( ~ r1_tsep_1(C_7,B_5)
      | ~ m1_pre_topc(B_5,C_7)
      | ~ m1_pre_topc(C_7,A_1)
      | v2_struct_0(C_7)
      | ~ m1_pre_topc(B_5,A_1)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_424,plain,(
    ! [B_64,A_1] :
      ( ~ m1_pre_topc(B_64,A_1)
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | k2_tsep_1('#skF_1',B_64,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_64)
      | ~ m1_pre_topc(B_64,'#skF_1')
      | v2_struct_0(B_64) ) ),
    inference(resolution,[status(thm)],[c_422,c_2])).

tff(c_577,plain,(
    ! [B_77,A_78] :
      ( ~ m1_pre_topc(B_77,A_78)
      | ~ m1_pre_topc('#skF_2',A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | k2_tsep_1('#skF_1',B_77,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_77)
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_424])).

tff(c_585,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_577])).

tff(c_600,plain,
    ( v2_struct_0('#skF_1')
    | k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_66,c_64,c_60,c_585])).

tff(c_602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_561,c_68,c_600])).

tff(c_603,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_608,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_603,c_4])).

tff(c_614,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_608])).

tff(c_642,plain,(
    ! [A_79] :
      ( ~ m1_pre_topc('#skF_3',A_79)
      | ~ m1_pre_topc('#skF_2',A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_614])).

tff(c_645,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_642])).

tff(c_651,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_645])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_651])).

tff(c_655,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_654,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_656,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_654])).

tff(c_1157,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_656])).

tff(c_1175,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_52,c_1157])).

tff(c_1176,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_54,c_1175])).

tff(c_1181,plain,(
    ~ r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1176])).

tff(c_12,plain,(
    ! [B_16,C_20,D_22,A_8] :
      ( r1_tsep_1(B_16,C_20)
      | ~ r1_tsep_1(D_22,C_20)
      | k2_tsep_1(A_8,C_20,k1_tsep_1(A_8,B_16,D_22)) = k2_tsep_1(A_8,C_20,B_16)
      | ~ m1_pre_topc(D_22,A_8)
      | v2_struct_0(D_22)
      | ~ m1_pre_topc(C_20,A_8)
      | v2_struct_0(C_20)
      | ~ m1_pre_topc(B_16,A_8)
      | v2_struct_0(B_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1303,plain,(
    ! [C_114,B_115,D_116,A_117] :
      ( r1_tsep_1(C_114,B_115)
      | ~ r1_tsep_1(C_114,D_116)
      | k2_tsep_1(A_117,C_114,k1_tsep_1(A_117,B_115,D_116)) = k2_tsep_1(A_117,C_114,B_115)
      | ~ m1_pre_topc(D_116,A_117)
      | v2_struct_0(D_116)
      | ~ m1_pre_topc(C_114,A_117)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_115,A_117)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1325,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2')
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1303,c_656])).

tff(c_1347,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_52,c_69,c_1325])).

tff(c_1348,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_54,c_1347])).

tff(c_1354,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1348])).

tff(c_1360,plain,
    ( k2_tsep_1('#skF_1','#skF_3','#skF_2') != k2_tsep_1('#skF_1','#skF_3','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1354])).

tff(c_1365,plain,
    ( k2_tsep_1('#skF_1','#skF_3','#skF_2') != k2_tsep_1('#skF_1','#skF_3','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_56,c_60,c_1360])).

tff(c_1366,plain,
    ( k2_tsep_1('#skF_1','#skF_3','#skF_2') != k2_tsep_1('#skF_1','#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_54,c_58,c_62,c_1181,c_1365])).

tff(c_1367,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1366])).

tff(c_1115,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_tsep_1(A_105,B_106,C_107) = g1_pre_topc(u1_struct_0(B_106),u1_pre_topc(B_106))
      | ~ m1_pre_topc(B_106,C_107)
      | r1_tsep_1(B_106,C_107)
      | ~ m1_pre_topc(C_107,A_105)
      | v2_struct_0(C_107)
      | ~ m1_pre_topc(B_106,A_105)
      | v2_struct_0(B_106)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1123,plain,(
    ! [B_106] :
      ( g1_pre_topc(u1_struct_0(B_106),u1_pre_topc(B_106)) = k2_tsep_1('#skF_1',B_106,'#skF_3')
      | ~ m1_pre_topc(B_106,'#skF_3')
      | r1_tsep_1(B_106,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_106,'#skF_1')
      | v2_struct_0(B_106)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_1115])).

tff(c_1136,plain,(
    ! [B_106] :
      ( g1_pre_topc(u1_struct_0(B_106),u1_pre_topc(B_106)) = k2_tsep_1('#skF_1',B_106,'#skF_3')
      | ~ m1_pre_topc(B_106,'#skF_3')
      | r1_tsep_1(B_106,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_106,'#skF_1')
      | v2_struct_0(B_106)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1123])).

tff(c_1383,plain,(
    ! [B_118] :
      ( g1_pre_topc(u1_struct_0(B_118),u1_pre_topc(B_118)) = k2_tsep_1('#skF_1',B_118,'#skF_3')
      | ~ m1_pre_topc(B_118,'#skF_3')
      | r1_tsep_1(B_118,'#skF_3')
      | ~ m1_pre_topc(B_118,'#skF_1')
      | v2_struct_0(B_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_1136])).

tff(c_1405,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) = k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1383,c_655])).

tff(c_1432,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) = k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1405])).

tff(c_1433,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) = k2_tsep_1('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1367,c_1432])).

tff(c_1458,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2')
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1433])).

tff(c_1471,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_52,c_69,c_1458])).

tff(c_1472,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_54,c_1471])).

tff(c_1684,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1472])).

tff(c_1686,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1684,c_2])).

tff(c_1691,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1686])).

tff(c_1696,plain,(
    ! [A_123] :
      ( ~ m1_pre_topc('#skF_3',A_123)
      | ~ m1_pre_topc('#skF_2',A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_1691])).

tff(c_1699,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1696])).

tff(c_1705,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_1699])).

tff(c_1707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1705])).

tff(c_1709,plain,(
    ~ r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1472])).

tff(c_1993,plain,(
    ! [C_129,B_130,D_131,A_132] :
      ( ~ r1_tsep_1(C_129,B_130)
      | r1_tsep_1(C_129,D_131)
      | k2_tsep_1(A_132,C_129,k1_tsep_1(A_132,B_130,D_131)) = k2_tsep_1(A_132,C_129,D_131)
      | ~ m1_pre_topc(D_131,A_132)
      | v2_struct_0(D_131)
      | ~ m1_pre_topc(C_129,A_132)
      | v2_struct_0(C_129)
      | ~ m1_pre_topc(B_130,A_132)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2010,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_1354])).

tff(c_2050,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_56,c_60,c_69,c_2010])).

tff(c_2052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_54,c_58,c_62,c_1709,c_2050])).

tff(c_2053,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1348])).

tff(c_2056,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2053,c_2])).

tff(c_2061,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2056])).

tff(c_2126,plain,(
    ! [A_133] :
      ( ~ m1_pre_topc('#skF_3',A_133)
      | ~ m1_pre_topc('#skF_2',A_133)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_2061])).

tff(c_2129,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2126])).

tff(c_2135,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_2129])).

tff(c_2137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2135])).

tff(c_2138,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4037,plain,(
    ! [B_231,C_232,D_233,A_234] :
      ( ~ r1_tsep_1(B_231,C_232)
      | r1_tsep_1(C_232,D_233)
      | k2_tsep_1(A_234,C_232,k1_tsep_1(A_234,B_231,D_233)) = k2_tsep_1(A_234,C_232,D_233)
      | ~ m1_pre_topc(D_233,A_234)
      | v2_struct_0(D_233)
      | ~ m1_pre_topc(C_232,A_234)
      | v2_struct_0(C_232)
      | ~ m1_pre_topc(B_231,A_234)
      | v2_struct_0(B_231)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3054,plain,(
    ! [A_190,B_191,C_192] :
      ( k2_tsep_1(A_190,B_191,C_192) = g1_pre_topc(u1_struct_0(B_191),u1_pre_topc(B_191))
      | ~ m1_pre_topc(B_191,C_192)
      | r1_tsep_1(B_191,C_192)
      | ~ m1_pre_topc(C_192,A_190)
      | v2_struct_0(C_192)
      | ~ m1_pre_topc(B_191,A_190)
      | v2_struct_0(B_191)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3062,plain,(
    ! [B_191] :
      ( g1_pre_topc(u1_struct_0(B_191),u1_pre_topc(B_191)) = k2_tsep_1('#skF_1',B_191,'#skF_3')
      | ~ m1_pre_topc(B_191,'#skF_3')
      | r1_tsep_1(B_191,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_191,'#skF_1')
      | v2_struct_0(B_191)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_3054])).

tff(c_3075,plain,(
    ! [B_191] :
      ( g1_pre_topc(u1_struct_0(B_191),u1_pre_topc(B_191)) = k2_tsep_1('#skF_1',B_191,'#skF_3')
      | ~ m1_pre_topc(B_191,'#skF_3')
      | r1_tsep_1(B_191,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_191,'#skF_1')
      | v2_struct_0(B_191)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3062])).

tff(c_3125,plain,(
    ! [B_194] :
      ( g1_pre_topc(u1_struct_0(B_194),u1_pre_topc(B_194)) = k2_tsep_1('#skF_1',B_194,'#skF_3')
      | ~ m1_pre_topc(B_194,'#skF_3')
      | r1_tsep_1(B_194,'#skF_3')
      | ~ m1_pre_topc(B_194,'#skF_1')
      | v2_struct_0(B_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_3075])).

tff(c_2538,plain,(
    ! [C_161,B_162,D_163,A_164] :
      ( r1_tsep_1(C_161,B_162)
      | ~ r1_tsep_1(D_163,C_161)
      | k2_tsep_1(A_164,C_161,k1_tsep_1(A_164,B_162,D_163)) = k2_tsep_1(A_164,C_161,B_162)
      | ~ m1_pre_topc(D_163,A_164)
      | v2_struct_0(D_163)
      | ~ m1_pre_topc(C_161,A_164)
      | v2_struct_0(C_161)
      | ~ m1_pre_topc(B_162,A_164)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2155,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_tsep_1(A_140,B_141,C_142) = g1_pre_topc(u1_struct_0(B_141),u1_pre_topc(B_141))
      | ~ m1_pre_topc(B_141,C_142)
      | r1_tsep_1(B_141,C_142)
      | ~ m1_pre_topc(C_142,A_140)
      | v2_struct_0(C_142)
      | ~ m1_pre_topc(B_141,A_140)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2163,plain,(
    ! [B_141] :
      ( g1_pre_topc(u1_struct_0(B_141),u1_pre_topc(B_141)) = k2_tsep_1('#skF_1',B_141,'#skF_3')
      | ~ m1_pre_topc(B_141,'#skF_3')
      | r1_tsep_1(B_141,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_141,'#skF_1')
      | v2_struct_0(B_141)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_2155])).

tff(c_2177,plain,(
    ! [B_141] :
      ( g1_pre_topc(u1_struct_0(B_141),u1_pre_topc(B_141)) = k2_tsep_1('#skF_1',B_141,'#skF_3')
      | ~ m1_pre_topc(B_141,'#skF_3')
      | r1_tsep_1(B_141,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_141,'#skF_1')
      | v2_struct_0(B_141)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2163])).

tff(c_2222,plain,(
    ! [B_148] :
      ( g1_pre_topc(u1_struct_0(B_148),u1_pre_topc(B_148)) = k2_tsep_1('#skF_1',B_148,'#skF_3')
      | ~ m1_pre_topc(B_148,'#skF_3')
      | r1_tsep_1(B_148,'#skF_3')
      | ~ m1_pre_topc(B_148,'#skF_1')
      | v2_struct_0(B_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_2177])).

tff(c_2153,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2236,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2222,c_2153])).

tff(c_2248,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_2236])).

tff(c_2249,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2248])).

tff(c_2251,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2249])).

tff(c_2549,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2538,c_2251])).

tff(c_2560,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_52,c_2138,c_2549])).

tff(c_2561,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_54,c_2560])).

tff(c_2563,plain,(
    k2_tsep_1('#skF_1','#skF_2','#skF_3') != k2_tsep_1('#skF_1','#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2561])).

tff(c_2178,plain,(
    ! [B_141] :
      ( g1_pre_topc(u1_struct_0(B_141),u1_pre_topc(B_141)) = k2_tsep_1('#skF_1',B_141,'#skF_3')
      | ~ m1_pre_topc(B_141,'#skF_3')
      | r1_tsep_1(B_141,'#skF_3')
      | ~ m1_pre_topc(B_141,'#skF_1')
      | v2_struct_0(B_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_2177])).

tff(c_2253,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_tsep_1(A_149,B_150,C_151) = g1_pre_topc(u1_struct_0(C_151),u1_pre_topc(C_151))
      | ~ m1_pre_topc(C_151,B_150)
      | r1_tsep_1(B_150,C_151)
      | ~ m1_pre_topc(C_151,A_149)
      | v2_struct_0(C_151)
      | ~ m1_pre_topc(B_150,A_149)
      | v2_struct_0(B_150)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2257,plain,(
    ! [B_150] :
      ( k2_tsep_1('#skF_1',B_150,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_150)
      | r1_tsep_1(B_150,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_150,'#skF_1')
      | v2_struct_0(B_150)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_2253])).

tff(c_2268,plain,(
    ! [B_150] :
      ( k2_tsep_1('#skF_1',B_150,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_150)
      | r1_tsep_1(B_150,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_150,'#skF_1')
      | v2_struct_0(B_150)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2257])).

tff(c_2338,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2268])).

tff(c_2365,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153)
      | ~ m1_pre_topc('#skF_2','#skF_3')
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_2338])).

tff(c_2391,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153)
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_2365])).

tff(c_2392,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153)
      | r1_tsep_1('#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2391])).

tff(c_2459,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2392])).

tff(c_2463,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2459,c_4])).

tff(c_2469,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2463])).

tff(c_2471,plain,(
    ! [A_155] :
      ( ~ m1_pre_topc('#skF_3',A_155)
      | ~ m1_pre_topc('#skF_2',A_155)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_2469])).

tff(c_2474,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2471])).

tff(c_2480,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_2474])).

tff(c_2482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2480])).

tff(c_2483,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153) ) ),
    inference(splitRight,[status(thm)],[c_2392])).

tff(c_2354,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2338,c_2153])).

tff(c_2544,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153)
      | r1_tsep_1('#skF_3','#skF_2')
      | ~ r1_tsep_1('#skF_4','#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2538,c_2354])).

tff(c_2557,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153)
      | r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_52,c_2138,c_2544])).

tff(c_2558,plain,(
    ! [B_153] :
      ( k2_tsep_1('#skF_1',B_153,'#skF_2') != k2_tsep_1('#skF_1','#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2',B_153)
      | r1_tsep_1(B_153,'#skF_2')
      | ~ m1_pre_topc(B_153,'#skF_1')
      | v2_struct_0(B_153)
      | r1_tsep_1('#skF_3','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_54,c_2557])).

tff(c_2564,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2558])).

tff(c_2566,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2564,c_2])).

tff(c_2571,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2566])).

tff(c_2575,plain,(
    ! [A_165] :
      ( ~ m1_pre_topc('#skF_3',A_165)
      | ~ m1_pre_topc('#skF_2',A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_2571])).

tff(c_2578,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2575])).

tff(c_2584,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_2578])).

tff(c_2586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2584])).

tff(c_2588,plain,(
    ~ r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2558])).

tff(c_2591,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2483,c_2588])).

tff(c_2595,plain,
    ( k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_2591])).

tff(c_2597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2563,c_2595])).

tff(c_2598,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2561])).

tff(c_2601,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2598,c_2])).

tff(c_2606,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2601])).

tff(c_2692,plain,(
    ! [A_170] :
      ( ~ m1_pre_topc('#skF_3',A_170)
      | ~ m1_pre_topc('#skF_2',A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_2606])).

tff(c_2695,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2692])).

tff(c_2701,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_2695])).

tff(c_2703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2701])).

tff(c_2704,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2249])).

tff(c_2709,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2704,c_4])).

tff(c_2715,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2709])).

tff(c_2717,plain,(
    ! [A_171] :
      ( ~ m1_pre_topc('#skF_3',A_171)
      | ~ m1_pre_topc('#skF_2',A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_2715])).

tff(c_2720,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2717])).

tff(c_2726,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_2720])).

tff(c_2728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2726])).

tff(c_2730,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3142,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) = k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3125,c_2730])).

tff(c_3166,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) = k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_3142])).

tff(c_3167,plain,
    ( k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) = k2_tsep_1('#skF_1','#skF_2','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3166])).

tff(c_3178,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3167])).

tff(c_3182,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_3178,c_4])).

tff(c_3187,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3182])).

tff(c_3189,plain,(
    ! [A_195] :
      ( ~ m1_pre_topc('#skF_3',A_195)
      | ~ m1_pre_topc('#skF_2',A_195)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_3187])).

tff(c_3192,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3189])).

tff(c_3198,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_3192])).

tff(c_3200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3198])).

tff(c_3201,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) = k2_tsep_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3167])).

tff(c_2737,plain,(
    ! [A_172,B_173,C_174] :
      ( k2_tsep_1(A_172,B_173,C_174) = g1_pre_topc(u1_struct_0(C_174),u1_pre_topc(C_174))
      | ~ m1_pre_topc(C_174,B_173)
      | r1_tsep_1(B_173,C_174)
      | ~ m1_pre_topc(C_174,A_172)
      | v2_struct_0(C_174)
      | ~ m1_pre_topc(B_173,A_172)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2741,plain,(
    ! [B_173] :
      ( k2_tsep_1('#skF_1',B_173,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_173)
      | r1_tsep_1(B_173,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_173,'#skF_1')
      | v2_struct_0(B_173)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_2737])).

tff(c_2752,plain,(
    ! [B_173] :
      ( k2_tsep_1('#skF_1',B_173,'#skF_2') = k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_2',B_173)
      | r1_tsep_1(B_173,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_173,'#skF_1')
      | v2_struct_0(B_173)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2730,c_2741])).

tff(c_2753,plain,(
    ! [B_173] :
      ( k2_tsep_1('#skF_1',B_173,'#skF_2') = k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_2',B_173)
      | r1_tsep_1(B_173,'#skF_2')
      | ~ m1_pre_topc(B_173,'#skF_1')
      | v2_struct_0(B_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2752])).

tff(c_3314,plain,(
    ! [B_199] :
      ( k2_tsep_1('#skF_1',B_199,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_199)
      | r1_tsep_1(B_199,'#skF_2')
      | ~ m1_pre_topc(B_199,'#skF_1')
      | v2_struct_0(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_2753])).

tff(c_3316,plain,(
    ! [B_199,A_1] :
      ( ~ m1_pre_topc(B_199,A_1)
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | k2_tsep_1('#skF_1',B_199,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_199)
      | ~ m1_pre_topc(B_199,'#skF_1')
      | v2_struct_0(B_199) ) ),
    inference(resolution,[status(thm)],[c_3314,c_2])).

tff(c_3541,plain,(
    ! [B_210,A_211] :
      ( ~ m1_pre_topc(B_210,A_211)
      | ~ m1_pre_topc('#skF_2',A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211)
      | k2_tsep_1('#skF_1',B_210,'#skF_2') = k2_tsep_1('#skF_1','#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_210)
      | ~ m1_pre_topc(B_210,'#skF_1')
      | v2_struct_0(B_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3316])).

tff(c_3549,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_3541])).

tff(c_3564,plain,
    ( v2_struct_0('#skF_1')
    | k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_66,c_64,c_60,c_3549])).

tff(c_3565,plain,(
    k2_tsep_1('#skF_1','#skF_2','#skF_3') = k2_tsep_1('#skF_1','#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_3564])).

tff(c_2729,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2731,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_2','#skF_4')) != k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_2729])).

tff(c_3270,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_2731])).

tff(c_3573,plain,(
    k2_tsep_1('#skF_1','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_2')) != k2_tsep_1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3565,c_3270])).

tff(c_4047,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4037,c_3573])).

tff(c_4085,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_56,c_60,c_2138,c_4047])).

tff(c_4086,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_54,c_58,c_62,c_4085])).

tff(c_4098,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4086,c_2])).

tff(c_4103,plain,(
    ! [A_1] :
      ( ~ m1_pre_topc('#skF_3',A_1)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4098])).

tff(c_4107,plain,(
    ! [A_235] :
      ( ~ m1_pre_topc('#skF_3',A_235)
      | ~ m1_pre_topc('#skF_2',A_235)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_4103])).

tff(c_4110,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_4107])).

tff(c_4116,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_4110])).

tff(c_4118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:24:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.40/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.40/2.24  
% 6.40/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.40/2.24  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.40/2.24  
% 6.40/2.24  %Foreground sorts:
% 6.40/2.24  
% 6.40/2.24  
% 6.40/2.24  %Background operators:
% 6.40/2.24  
% 6.40/2.24  
% 6.40/2.24  %Foreground operators:
% 6.40/2.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.40/2.24  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 6.40/2.24  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.40/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.40/2.24  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.40/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.40/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.40/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.40/2.24  tff('#skF_1', type, '#skF_1': $i).
% 6.40/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.40/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.40/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.40/2.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.40/2.24  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 6.40/2.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.40/2.24  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 6.40/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.40/2.24  
% 6.40/2.28  tff(f_183, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | ((k2_tsep_1(A, C, k1_tsep_1(A, B, D)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (k2_tsep_1(A, C, k1_tsep_1(A, D, B)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tmap_1)).
% 6.40/2.28  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~(((r1_tsep_1(B, C) | r1_tsep_1(C, B)) & ~(r1_tsep_1(D, C) & r1_tsep_1(C, D))) & ~((k2_tsep_1(A, k1_tsep_1(A, B, D), C) = k2_tsep_1(A, D, C)) & (k2_tsep_1(A, C, k1_tsep_1(A, B, D)) = k2_tsep_1(A, C, D)))) & ~((~(r1_tsep_1(B, C) & r1_tsep_1(C, B)) & (r1_tsep_1(D, C) | r1_tsep_1(C, D))) & ~((k2_tsep_1(A, k1_tsep_1(A, B, D), C) = k2_tsep_1(A, B, C)) & (k2_tsep_1(A, C, k1_tsep_1(A, B, D)) = k2_tsep_1(A, C, B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tmap_1)).
% 6.40/2.28  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => ((((m1_pre_topc(B, C) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => m1_pre_topc(B, C))) & (m1_pre_topc(C, B) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => m1_pre_topc(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tsep_1)).
% 6.40/2.28  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 6.40/2.28  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_56, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_60, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_50, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_48, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_69, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 6.40/2.28  tff(c_6, plain, (![C_20, B_16, D_22, A_8]: (r1_tsep_1(C_20, B_16) | ~r1_tsep_1(C_20, D_22) | k2_tsep_1(A_8, C_20, k1_tsep_1(A_8, B_16, D_22))=k2_tsep_1(A_8, C_20, B_16) | ~m1_pre_topc(D_22, A_8) | v2_struct_0(D_22) | ~m1_pre_topc(C_20, A_8) | v2_struct_0(C_20) | ~m1_pre_topc(B_16, A_8) | v2_struct_0(B_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_1138, plain, (![B_108, C_109, D_110, A_111]: (r1_tsep_1(B_108, C_109) | ~r1_tsep_1(D_110, C_109) | k2_tsep_1(A_111, C_109, k1_tsep_1(A_111, B_108, D_110))=k2_tsep_1(A_111, C_109, B_108) | ~m1_pre_topc(D_110, A_111) | v2_struct_0(D_110) | ~m1_pre_topc(C_109, A_111) | v2_struct_0(C_109) | ~m1_pre_topc(B_108, A_111) | v2_struct_0(B_108) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_176, plain, (![A_54, B_55, C_56]: (k2_tsep_1(A_54, B_55, C_56)=g1_pre_topc(u1_struct_0(B_55), u1_pre_topc(B_55)) | ~m1_pre_topc(B_55, C_56) | r1_tsep_1(B_55, C_56) | ~m1_pre_topc(C_56, A_54) | v2_struct_0(C_56) | ~m1_pre_topc(B_55, A_54) | v2_struct_0(B_55) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.40/2.28  tff(c_184, plain, (![B_55]: (g1_pre_topc(u1_struct_0(B_55), u1_pre_topc(B_55))=k2_tsep_1('#skF_1', B_55, '#skF_3') | ~m1_pre_topc(B_55, '#skF_3') | r1_tsep_1(B_55, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_55, '#skF_1') | v2_struct_0(B_55) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_176])).
% 6.40/2.28  tff(c_198, plain, (![B_55]: (g1_pre_topc(u1_struct_0(B_55), u1_pre_topc(B_55))=k2_tsep_1('#skF_1', B_55, '#skF_3') | ~m1_pre_topc(B_55, '#skF_3') | r1_tsep_1(B_55, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_55, '#skF_1') | v2_struct_0(B_55) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_184])).
% 6.40/2.28  tff(c_310, plain, (![B_59]: (g1_pre_topc(u1_struct_0(B_59), u1_pre_topc(B_59))=k2_tsep_1('#skF_1', B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | r1_tsep_1(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_1') | v2_struct_0(B_59))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_198])).
% 6.40/2.28  tff(c_85, plain, (![A_47, B_48, C_49]: (k2_tsep_1(A_47, B_48, C_49)=g1_pre_topc(u1_struct_0(C_49), u1_pre_topc(C_49)) | ~m1_pre_topc(C_49, B_48) | r1_tsep_1(B_48, C_49) | ~m1_pre_topc(C_49, A_47) | v2_struct_0(C_49) | ~m1_pre_topc(B_48, A_47) | v2_struct_0(B_48) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.40/2.28  tff(c_89, plain, (![B_48]: (k2_tsep_1('#skF_1', B_48, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_48) | r1_tsep_1(B_48, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_48, '#skF_1') | v2_struct_0(B_48) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_85])).
% 6.40/2.28  tff(c_100, plain, (![B_48]: (k2_tsep_1('#skF_1', B_48, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_48) | r1_tsep_1(B_48, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_48, '#skF_1') | v2_struct_0(B_48) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_89])).
% 6.40/2.28  tff(c_101, plain, (![B_48]: (k2_tsep_1('#skF_1', B_48, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_48) | r1_tsep_1(B_48, '#skF_2') | ~m1_pre_topc(B_48, '#skF_1') | v2_struct_0(B_48))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_100])).
% 6.40/2.28  tff(c_325, plain, (![B_48]: (k2_tsep_1('#skF_1', B_48, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_48) | r1_tsep_1(B_48, '#skF_2') | ~m1_pre_topc(B_48, '#skF_1') | v2_struct_0(B_48) | ~m1_pre_topc('#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_310, c_101])).
% 6.40/2.28  tff(c_355, plain, (![B_48]: (k2_tsep_1('#skF_1', B_48, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_48) | r1_tsep_1(B_48, '#skF_2') | ~m1_pre_topc(B_48, '#skF_1') | v2_struct_0(B_48) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_325])).
% 6.40/2.28  tff(c_356, plain, (![B_48]: (k2_tsep_1('#skF_1', B_48, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_48) | r1_tsep_1(B_48, '#skF_2') | ~m1_pre_topc(B_48, '#skF_1') | v2_struct_0(B_48) | r1_tsep_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_355])).
% 6.40/2.28  tff(c_390, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_356])).
% 6.40/2.28  tff(c_4, plain, (![B_5, C_7, A_1]: (~r1_tsep_1(B_5, C_7) | ~m1_pre_topc(B_5, C_7) | ~m1_pre_topc(C_7, A_1) | v2_struct_0(C_7) | ~m1_pre_topc(B_5, A_1) | v2_struct_0(B_5) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.40/2.28  tff(c_394, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_390, c_4])).
% 6.40/2.28  tff(c_400, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_394])).
% 6.40/2.28  tff(c_402, plain, (![A_63]: (~m1_pre_topc('#skF_3', A_63) | ~m1_pre_topc('#skF_2', A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_400])).
% 6.40/2.28  tff(c_405, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_402])).
% 6.40/2.28  tff(c_411, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_405])).
% 6.40/2.28  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_411])).
% 6.40/2.28  tff(c_415, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_356])).
% 6.40/2.28  tff(c_533, plain, (![B_72, C_73, D_74, A_75]: (r1_tsep_1(B_72, C_73) | ~r1_tsep_1(C_73, D_74) | k2_tsep_1(A_75, C_73, k1_tsep_1(A_75, B_72, D_74))=k2_tsep_1(A_75, C_73, B_72) | ~m1_pre_topc(D_74, A_75) | v2_struct_0(D_74) | ~m1_pre_topc(C_73, A_75) | v2_struct_0(C_73) | ~m1_pre_topc(B_72, A_75) | v2_struct_0(B_72) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2')) | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.40/2.28  tff(c_84, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 6.40/2.28  tff(c_331, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_310, c_84])).
% 6.40/2.28  tff(c_361, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_331])).
% 6.40/2.28  tff(c_362, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_361])).
% 6.40/2.28  tff(c_373, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_362])).
% 6.40/2.28  tff(c_547, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_533, c_373])).
% 6.40/2.28  tff(c_560, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_52, c_69, c_547])).
% 6.40/2.28  tff(c_561, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_54, c_415, c_560])).
% 6.40/2.28  tff(c_422, plain, (![B_64]: (k2_tsep_1('#skF_1', B_64, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_64) | r1_tsep_1(B_64, '#skF_2') | ~m1_pre_topc(B_64, '#skF_1') | v2_struct_0(B_64))), inference(splitRight, [status(thm)], [c_356])).
% 6.40/2.28  tff(c_2, plain, (![C_7, B_5, A_1]: (~r1_tsep_1(C_7, B_5) | ~m1_pre_topc(B_5, C_7) | ~m1_pre_topc(C_7, A_1) | v2_struct_0(C_7) | ~m1_pre_topc(B_5, A_1) | v2_struct_0(B_5) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.40/2.28  tff(c_424, plain, (![B_64, A_1]: (~m1_pre_topc(B_64, A_1) | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | k2_tsep_1('#skF_1', B_64, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_64) | ~m1_pre_topc(B_64, '#skF_1') | v2_struct_0(B_64))), inference(resolution, [status(thm)], [c_422, c_2])).
% 6.40/2.28  tff(c_577, plain, (![B_77, A_78]: (~m1_pre_topc(B_77, A_78) | ~m1_pre_topc('#skF_2', A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | k2_tsep_1('#skF_1', B_77, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_77) | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(negUnitSimplification, [status(thm)], [c_62, c_424])).
% 6.40/2.28  tff(c_585, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_577])).
% 6.40/2.28  tff(c_600, plain, (v2_struct_0('#skF_1') | k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_66, c_64, c_60, c_585])).
% 6.40/2.28  tff(c_602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_561, c_68, c_600])).
% 6.40/2.28  tff(c_603, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_362])).
% 6.40/2.28  tff(c_608, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_603, c_4])).
% 6.40/2.28  tff(c_614, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_608])).
% 6.40/2.28  tff(c_642, plain, (![A_79]: (~m1_pre_topc('#skF_3', A_79) | ~m1_pre_topc('#skF_2', A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_614])).
% 6.40/2.28  tff(c_645, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_642])).
% 6.40/2.28  tff(c_651, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_645])).
% 6.40/2.28  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_651])).
% 6.40/2.28  tff(c_655, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 6.40/2.28  tff(c_654, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 6.40/2.28  tff(c_656, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_655, c_654])).
% 6.40/2.28  tff(c_1157, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1138, c_656])).
% 6.40/2.28  tff(c_1175, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_52, c_1157])).
% 6.40/2.28  tff(c_1176, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_54, c_1175])).
% 6.40/2.28  tff(c_1181, plain, (~r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1176])).
% 6.40/2.28  tff(c_12, plain, (![B_16, C_20, D_22, A_8]: (r1_tsep_1(B_16, C_20) | ~r1_tsep_1(D_22, C_20) | k2_tsep_1(A_8, C_20, k1_tsep_1(A_8, B_16, D_22))=k2_tsep_1(A_8, C_20, B_16) | ~m1_pre_topc(D_22, A_8) | v2_struct_0(D_22) | ~m1_pre_topc(C_20, A_8) | v2_struct_0(C_20) | ~m1_pre_topc(B_16, A_8) | v2_struct_0(B_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_1303, plain, (![C_114, B_115, D_116, A_117]: (r1_tsep_1(C_114, B_115) | ~r1_tsep_1(C_114, D_116) | k2_tsep_1(A_117, C_114, k1_tsep_1(A_117, B_115, D_116))=k2_tsep_1(A_117, C_114, B_115) | ~m1_pre_topc(D_116, A_117) | v2_struct_0(D_116) | ~m1_pre_topc(C_114, A_117) | v2_struct_0(C_114) | ~m1_pre_topc(B_115, A_117) | v2_struct_0(B_115) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_1325, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1303, c_656])).
% 6.40/2.28  tff(c_1347, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_52, c_69, c_1325])).
% 6.40/2.28  tff(c_1348, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_54, c_1347])).
% 6.40/2.28  tff(c_1354, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1348])).
% 6.40/2.28  tff(c_1360, plain, (k2_tsep_1('#skF_1', '#skF_3', '#skF_2')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_1354])).
% 6.40/2.28  tff(c_1365, plain, (k2_tsep_1('#skF_1', '#skF_3', '#skF_2')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_56, c_60, c_1360])).
% 6.40/2.28  tff(c_1366, plain, (k2_tsep_1('#skF_1', '#skF_3', '#skF_2')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_54, c_58, c_62, c_1181, c_1365])).
% 6.40/2.28  tff(c_1367, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_1366])).
% 6.40/2.28  tff(c_1115, plain, (![A_105, B_106, C_107]: (k2_tsep_1(A_105, B_106, C_107)=g1_pre_topc(u1_struct_0(B_106), u1_pre_topc(B_106)) | ~m1_pre_topc(B_106, C_107) | r1_tsep_1(B_106, C_107) | ~m1_pre_topc(C_107, A_105) | v2_struct_0(C_107) | ~m1_pre_topc(B_106, A_105) | v2_struct_0(B_106) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.40/2.28  tff(c_1123, plain, (![B_106]: (g1_pre_topc(u1_struct_0(B_106), u1_pre_topc(B_106))=k2_tsep_1('#skF_1', B_106, '#skF_3') | ~m1_pre_topc(B_106, '#skF_3') | r1_tsep_1(B_106, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_106, '#skF_1') | v2_struct_0(B_106) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_1115])).
% 6.40/2.28  tff(c_1136, plain, (![B_106]: (g1_pre_topc(u1_struct_0(B_106), u1_pre_topc(B_106))=k2_tsep_1('#skF_1', B_106, '#skF_3') | ~m1_pre_topc(B_106, '#skF_3') | r1_tsep_1(B_106, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_106, '#skF_1') | v2_struct_0(B_106) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1123])).
% 6.40/2.28  tff(c_1383, plain, (![B_118]: (g1_pre_topc(u1_struct_0(B_118), u1_pre_topc(B_118))=k2_tsep_1('#skF_1', B_118, '#skF_3') | ~m1_pre_topc(B_118, '#skF_3') | r1_tsep_1(B_118, '#skF_3') | ~m1_pre_topc(B_118, '#skF_1') | v2_struct_0(B_118))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_1136])).
% 6.40/2.28  tff(c_1405, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1383, c_655])).
% 6.40/2.28  tff(c_1432, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1405])).
% 6.40/2.28  tff(c_1433, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))=k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_1367, c_1432])).
% 6.40/2.28  tff(c_1458, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_1433])).
% 6.40/2.28  tff(c_1471, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_52, c_69, c_1458])).
% 6.40/2.28  tff(c_1472, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_54, c_1471])).
% 6.40/2.28  tff(c_1684, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1472])).
% 6.40/2.28  tff(c_1686, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_1684, c_2])).
% 6.40/2.28  tff(c_1691, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1686])).
% 6.40/2.28  tff(c_1696, plain, (![A_123]: (~m1_pre_topc('#skF_3', A_123) | ~m1_pre_topc('#skF_2', A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_1691])).
% 6.40/2.28  tff(c_1699, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_1696])).
% 6.40/2.28  tff(c_1705, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_1699])).
% 6.40/2.28  tff(c_1707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1705])).
% 6.40/2.28  tff(c_1709, plain, (~r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1472])).
% 6.40/2.28  tff(c_1993, plain, (![C_129, B_130, D_131, A_132]: (~r1_tsep_1(C_129, B_130) | r1_tsep_1(C_129, D_131) | k2_tsep_1(A_132, C_129, k1_tsep_1(A_132, B_130, D_131))=k2_tsep_1(A_132, C_129, D_131) | ~m1_pre_topc(D_131, A_132) | v2_struct_0(D_131) | ~m1_pre_topc(C_129, A_132) | v2_struct_0(C_129) | ~m1_pre_topc(B_130, A_132) | v2_struct_0(B_130) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_2010, plain, (~r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1993, c_1354])).
% 6.40/2.28  tff(c_2050, plain, (r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_56, c_60, c_69, c_2010])).
% 6.40/2.28  tff(c_2052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_54, c_58, c_62, c_1709, c_2050])).
% 6.40/2.28  tff(c_2053, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1348])).
% 6.40/2.28  tff(c_2056, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_2053, c_2])).
% 6.40/2.28  tff(c_2061, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2056])).
% 6.40/2.28  tff(c_2126, plain, (![A_133]: (~m1_pre_topc('#skF_3', A_133) | ~m1_pre_topc('#skF_2', A_133) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_2061])).
% 6.40/2.28  tff(c_2129, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2126])).
% 6.40/2.28  tff(c_2135, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_2129])).
% 6.40/2.28  tff(c_2137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2135])).
% 6.40/2.28  tff(c_2138, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 6.40/2.28  tff(c_4037, plain, (![B_231, C_232, D_233, A_234]: (~r1_tsep_1(B_231, C_232) | r1_tsep_1(C_232, D_233) | k2_tsep_1(A_234, C_232, k1_tsep_1(A_234, B_231, D_233))=k2_tsep_1(A_234, C_232, D_233) | ~m1_pre_topc(D_233, A_234) | v2_struct_0(D_233) | ~m1_pre_topc(C_232, A_234) | v2_struct_0(C_232) | ~m1_pre_topc(B_231, A_234) | v2_struct_0(B_231) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_3054, plain, (![A_190, B_191, C_192]: (k2_tsep_1(A_190, B_191, C_192)=g1_pre_topc(u1_struct_0(B_191), u1_pre_topc(B_191)) | ~m1_pre_topc(B_191, C_192) | r1_tsep_1(B_191, C_192) | ~m1_pre_topc(C_192, A_190) | v2_struct_0(C_192) | ~m1_pre_topc(B_191, A_190) | v2_struct_0(B_191) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.40/2.28  tff(c_3062, plain, (![B_191]: (g1_pre_topc(u1_struct_0(B_191), u1_pre_topc(B_191))=k2_tsep_1('#skF_1', B_191, '#skF_3') | ~m1_pre_topc(B_191, '#skF_3') | r1_tsep_1(B_191, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_191, '#skF_1') | v2_struct_0(B_191) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_3054])).
% 6.40/2.28  tff(c_3075, plain, (![B_191]: (g1_pre_topc(u1_struct_0(B_191), u1_pre_topc(B_191))=k2_tsep_1('#skF_1', B_191, '#skF_3') | ~m1_pre_topc(B_191, '#skF_3') | r1_tsep_1(B_191, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_191, '#skF_1') | v2_struct_0(B_191) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3062])).
% 6.40/2.28  tff(c_3125, plain, (![B_194]: (g1_pre_topc(u1_struct_0(B_194), u1_pre_topc(B_194))=k2_tsep_1('#skF_1', B_194, '#skF_3') | ~m1_pre_topc(B_194, '#skF_3') | r1_tsep_1(B_194, '#skF_3') | ~m1_pre_topc(B_194, '#skF_1') | v2_struct_0(B_194))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_3075])).
% 6.40/2.28  tff(c_2538, plain, (![C_161, B_162, D_163, A_164]: (r1_tsep_1(C_161, B_162) | ~r1_tsep_1(D_163, C_161) | k2_tsep_1(A_164, C_161, k1_tsep_1(A_164, B_162, D_163))=k2_tsep_1(A_164, C_161, B_162) | ~m1_pre_topc(D_163, A_164) | v2_struct_0(D_163) | ~m1_pre_topc(C_161, A_164) | v2_struct_0(C_161) | ~m1_pre_topc(B_162, A_164) | v2_struct_0(B_162) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.40/2.28  tff(c_2155, plain, (![A_140, B_141, C_142]: (k2_tsep_1(A_140, B_141, C_142)=g1_pre_topc(u1_struct_0(B_141), u1_pre_topc(B_141)) | ~m1_pre_topc(B_141, C_142) | r1_tsep_1(B_141, C_142) | ~m1_pre_topc(C_142, A_140) | v2_struct_0(C_142) | ~m1_pre_topc(B_141, A_140) | v2_struct_0(B_141) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.40/2.28  tff(c_2163, plain, (![B_141]: (g1_pre_topc(u1_struct_0(B_141), u1_pre_topc(B_141))=k2_tsep_1('#skF_1', B_141, '#skF_3') | ~m1_pre_topc(B_141, '#skF_3') | r1_tsep_1(B_141, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_141, '#skF_1') | v2_struct_0(B_141) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_2155])).
% 6.40/2.28  tff(c_2177, plain, (![B_141]: (g1_pre_topc(u1_struct_0(B_141), u1_pre_topc(B_141))=k2_tsep_1('#skF_1', B_141, '#skF_3') | ~m1_pre_topc(B_141, '#skF_3') | r1_tsep_1(B_141, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_141, '#skF_1') | v2_struct_0(B_141) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2163])).
% 6.40/2.28  tff(c_2222, plain, (![B_148]: (g1_pre_topc(u1_struct_0(B_148), u1_pre_topc(B_148))=k2_tsep_1('#skF_1', B_148, '#skF_3') | ~m1_pre_topc(B_148, '#skF_3') | r1_tsep_1(B_148, '#skF_3') | ~m1_pre_topc(B_148, '#skF_1') | v2_struct_0(B_148))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_2177])).
% 6.40/2.28  tff(c_2153, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 6.40/2.28  tff(c_2236, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2222, c_2153])).
% 6.40/2.28  tff(c_2248, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_2236])).
% 6.40/2.28  tff(c_2249, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_2248])).
% 6.40/2.28  tff(c_2251, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_2249])).
% 6.40/2.28  tff(c_2549, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2') | ~r1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2538, c_2251])).
% 6.40/2.28  tff(c_2560, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_52, c_2138, c_2549])).
% 6.40/2.28  tff(c_2561, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | r1_tsep_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_54, c_2560])).
% 6.40/2.28  tff(c_2563, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2561])).
% 6.40/2.28  tff(c_2178, plain, (![B_141]: (g1_pre_topc(u1_struct_0(B_141), u1_pre_topc(B_141))=k2_tsep_1('#skF_1', B_141, '#skF_3') | ~m1_pre_topc(B_141, '#skF_3') | r1_tsep_1(B_141, '#skF_3') | ~m1_pre_topc(B_141, '#skF_1') | v2_struct_0(B_141))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_2177])).
% 6.40/2.28  tff(c_2253, plain, (![A_149, B_150, C_151]: (k2_tsep_1(A_149, B_150, C_151)=g1_pre_topc(u1_struct_0(C_151), u1_pre_topc(C_151)) | ~m1_pre_topc(C_151, B_150) | r1_tsep_1(B_150, C_151) | ~m1_pre_topc(C_151, A_149) | v2_struct_0(C_151) | ~m1_pre_topc(B_150, A_149) | v2_struct_0(B_150) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.40/2.28  tff(c_2257, plain, (![B_150]: (k2_tsep_1('#skF_1', B_150, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_150) | r1_tsep_1(B_150, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_150, '#skF_1') | v2_struct_0(B_150) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_2253])).
% 6.40/2.28  tff(c_2268, plain, (![B_150]: (k2_tsep_1('#skF_1', B_150, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_150) | r1_tsep_1(B_150, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_150, '#skF_1') | v2_struct_0(B_150) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2257])).
% 6.40/2.28  tff(c_2338, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2268])).
% 6.40/2.28  tff(c_2365, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153) | ~m1_pre_topc('#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2178, c_2338])).
% 6.40/2.28  tff(c_2391, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_2365])).
% 6.40/2.28  tff(c_2392, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153) | r1_tsep_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_2391])).
% 6.40/2.28  tff(c_2459, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_2392])).
% 6.40/2.28  tff(c_2463, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_2459, c_4])).
% 6.40/2.28  tff(c_2469, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2463])).
% 6.40/2.28  tff(c_2471, plain, (![A_155]: (~m1_pre_topc('#skF_3', A_155) | ~m1_pre_topc('#skF_2', A_155) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_2469])).
% 6.40/2.28  tff(c_2474, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2471])).
% 6.40/2.28  tff(c_2480, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_2474])).
% 6.40/2.28  tff(c_2482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2480])).
% 6.40/2.28  tff(c_2483, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153))), inference(splitRight, [status(thm)], [c_2392])).
% 6.40/2.28  tff(c_2354, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153))), inference(superposition, [status(thm), theory('equality')], [c_2338, c_2153])).
% 6.40/2.28  tff(c_2544, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153) | r1_tsep_1('#skF_3', '#skF_2') | ~r1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2538, c_2354])).
% 6.40/2.28  tff(c_2557, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153) | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_52, c_2138, c_2544])).
% 6.40/2.28  tff(c_2558, plain, (![B_153]: (k2_tsep_1('#skF_1', B_153, '#skF_2')!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', B_153) | r1_tsep_1(B_153, '#skF_2') | ~m1_pre_topc(B_153, '#skF_1') | v2_struct_0(B_153) | r1_tsep_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_54, c_2557])).
% 6.40/2.28  tff(c_2564, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2558])).
% 6.40/2.28  tff(c_2566, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_2564, c_2])).
% 6.40/2.28  tff(c_2571, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2566])).
% 6.40/2.28  tff(c_2575, plain, (![A_165]: (~m1_pre_topc('#skF_3', A_165) | ~m1_pre_topc('#skF_2', A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_2571])).
% 6.40/2.28  tff(c_2578, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2575])).
% 6.40/2.28  tff(c_2584, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_2578])).
% 6.40/2.28  tff(c_2586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2584])).
% 6.40/2.28  tff(c_2588, plain, (~r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_2558])).
% 6.40/2.28  tff(c_2591, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2483, c_2588])).
% 6.40/2.28  tff(c_2595, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_2591])).
% 6.40/2.28  tff(c_2597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2563, c_2595])).
% 6.40/2.28  tff(c_2598, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_2561])).
% 6.40/2.28  tff(c_2601, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_2598, c_2])).
% 6.40/2.28  tff(c_2606, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2601])).
% 6.40/2.28  tff(c_2692, plain, (![A_170]: (~m1_pre_topc('#skF_3', A_170) | ~m1_pre_topc('#skF_2', A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_2606])).
% 6.40/2.28  tff(c_2695, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2692])).
% 6.40/2.28  tff(c_2701, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_2695])).
% 6.40/2.28  tff(c_2703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2701])).
% 6.40/2.28  tff(c_2704, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_2249])).
% 6.40/2.28  tff(c_2709, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_2704, c_4])).
% 6.40/2.28  tff(c_2715, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2709])).
% 6.40/2.28  tff(c_2717, plain, (![A_171]: (~m1_pre_topc('#skF_3', A_171) | ~m1_pre_topc('#skF_2', A_171) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_2715])).
% 6.40/2.28  tff(c_2720, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2717])).
% 6.40/2.28  tff(c_2726, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_2720])).
% 6.40/2.28  tff(c_2728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2726])).
% 6.40/2.28  tff(c_2730, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 6.40/2.28  tff(c_3142, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3125, c_2730])).
% 6.40/2.28  tff(c_3166, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_3142])).
% 6.40/2.28  tff(c_3167, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_3166])).
% 6.40/2.28  tff(c_3178, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_3167])).
% 6.40/2.28  tff(c_3182, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_3178, c_4])).
% 6.40/2.28  tff(c_3187, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3182])).
% 6.40/2.28  tff(c_3189, plain, (![A_195]: (~m1_pre_topc('#skF_3', A_195) | ~m1_pre_topc('#skF_2', A_195) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_3187])).
% 6.40/2.28  tff(c_3192, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3189])).
% 6.40/2.28  tff(c_3198, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_3192])).
% 6.40/2.28  tff(c_3200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3198])).
% 6.40/2.28  tff(c_3201, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))=k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_3167])).
% 6.40/2.28  tff(c_2737, plain, (![A_172, B_173, C_174]: (k2_tsep_1(A_172, B_173, C_174)=g1_pre_topc(u1_struct_0(C_174), u1_pre_topc(C_174)) | ~m1_pre_topc(C_174, B_173) | r1_tsep_1(B_173, C_174) | ~m1_pre_topc(C_174, A_172) | v2_struct_0(C_174) | ~m1_pre_topc(B_173, A_172) | v2_struct_0(B_173) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.40/2.28  tff(c_2741, plain, (![B_173]: (k2_tsep_1('#skF_1', B_173, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_173) | r1_tsep_1(B_173, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_173, '#skF_1') | v2_struct_0(B_173) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_2737])).
% 6.40/2.28  tff(c_2752, plain, (![B_173]: (k2_tsep_1('#skF_1', B_173, '#skF_2')=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_2', B_173) | r1_tsep_1(B_173, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_173, '#skF_1') | v2_struct_0(B_173) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2730, c_2741])).
% 6.40/2.28  tff(c_2753, plain, (![B_173]: (k2_tsep_1('#skF_1', B_173, '#skF_2')=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_2', B_173) | r1_tsep_1(B_173, '#skF_2') | ~m1_pre_topc(B_173, '#skF_1') | v2_struct_0(B_173))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2752])).
% 6.40/2.28  tff(c_3314, plain, (![B_199]: (k2_tsep_1('#skF_1', B_199, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_199) | r1_tsep_1(B_199, '#skF_2') | ~m1_pre_topc(B_199, '#skF_1') | v2_struct_0(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_2753])).
% 6.40/2.28  tff(c_3316, plain, (![B_199, A_1]: (~m1_pre_topc(B_199, A_1) | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | k2_tsep_1('#skF_1', B_199, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_199) | ~m1_pre_topc(B_199, '#skF_1') | v2_struct_0(B_199))), inference(resolution, [status(thm)], [c_3314, c_2])).
% 6.40/2.28  tff(c_3541, plain, (![B_210, A_211]: (~m1_pre_topc(B_210, A_211) | ~m1_pre_topc('#skF_2', A_211) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211) | v2_struct_0(A_211) | k2_tsep_1('#skF_1', B_210, '#skF_2')=k2_tsep_1('#skF_1', '#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_210) | ~m1_pre_topc(B_210, '#skF_1') | v2_struct_0(B_210))), inference(negUnitSimplification, [status(thm)], [c_62, c_3316])).
% 6.40/2.28  tff(c_3549, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_3541])).
% 6.40/2.28  tff(c_3564, plain, (v2_struct_0('#skF_1') | k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_66, c_64, c_60, c_3549])).
% 6.40/2.28  tff(c_3565, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_3')=k2_tsep_1('#skF_1', '#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_3564])).
% 6.40/2.28  tff(c_2729, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 6.40/2.28  tff(c_2731, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_2', '#skF_4'))!=k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2730, c_2729])).
% 6.40/2.28  tff(c_3270, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_2731])).
% 6.40/2.28  tff(c_3573, plain, (k2_tsep_1('#skF_1', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_2'))!=k2_tsep_1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3565, c_3270])).
% 6.40/2.28  tff(c_4047, plain, (~r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4037, c_3573])).
% 6.40/2.28  tff(c_4085, plain, (r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_56, c_60, c_2138, c_4047])).
% 6.40/2.28  tff(c_4086, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_54, c_58, c_62, c_4085])).
% 6.40/2.28  tff(c_4098, plain, (![A_1]: (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_4086, c_2])).
% 6.40/2.28  tff(c_4103, plain, (![A_1]: (~m1_pre_topc('#skF_3', A_1) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4098])).
% 6.40/2.28  tff(c_4107, plain, (![A_235]: (~m1_pre_topc('#skF_3', A_235) | ~m1_pre_topc('#skF_2', A_235) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_4103])).
% 6.40/2.28  tff(c_4110, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_4107])).
% 6.40/2.28  tff(c_4116, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_4110])).
% 6.40/2.28  tff(c_4118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_4116])).
% 6.40/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.40/2.28  
% 6.40/2.28  Inference rules
% 6.40/2.28  ----------------------
% 6.40/2.28  #Ref     : 0
% 6.40/2.28  #Sup     : 807
% 6.40/2.28  #Fact    : 12
% 6.40/2.28  #Define  : 0
% 6.40/2.28  #Split   : 50
% 6.40/2.28  #Chain   : 0
% 6.40/2.28  #Close   : 0
% 6.40/2.28  
% 6.40/2.28  Ordering : KBO
% 6.40/2.28  
% 6.40/2.28  Simplification rules
% 6.40/2.28  ----------------------
% 6.40/2.28  #Subsume      : 217
% 6.40/2.28  #Demod        : 977
% 6.40/2.28  #Tautology    : 180
% 6.40/2.28  #SimpNegUnit  : 483
% 6.40/2.28  #BackRed      : 28
% 6.40/2.28  
% 6.40/2.28  #Partial instantiations: 0
% 6.40/2.28  #Strategies tried      : 1
% 6.40/2.28  
% 6.40/2.28  Timing (in seconds)
% 6.40/2.28  ----------------------
% 6.40/2.28  Preprocessing        : 0.40
% 6.40/2.28  Parsing              : 0.21
% 6.40/2.28  CNF conversion       : 0.04
% 6.40/2.28  Main loop            : 1.06
% 6.40/2.28  Inferencing          : 0.35
% 6.40/2.28  Reduction            : 0.32
% 6.40/2.28  Demodulation         : 0.20
% 6.40/2.28  BG Simplification    : 0.06
% 6.40/2.28  Subsumption          : 0.28
% 6.40/2.28  Abstraction          : 0.07
% 6.40/2.28  MUC search           : 0.00
% 6.40/2.28  Cooper               : 0.00
% 6.40/2.28  Total                : 1.54
% 6.40/2.28  Index Insertion      : 0.00
% 6.40/2.28  Index Deletion       : 0.00
% 6.40/2.28  Index Matching       : 0.00
% 6.40/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
