%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:51 EST 2020

% Result     : Theorem 11.20s
% Output     : CNFRefutation 11.35s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 445 expanded)
%              Number of leaves         :   36 ( 160 expanded)
%              Depth                    :   21
%              Number of atoms          :  269 (1321 expanded)
%              Number of equality atoms :   36 ( 215 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_34,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ v2_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_98,plain,(
    ~ v2_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_542,plain,(
    ! [B_129,A_130] :
      ( v2_tops_1(B_129,A_130)
      | k1_tops_1(A_130,B_129) != k1_xboole_0
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_549,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | k1_tops_1('#skF_4','#skF_5') != k1_xboole_0
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_542])).

tff(c_553,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | k1_tops_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_549])).

tff(c_554,plain,(
    k1_tops_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_553])).

tff(c_260,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k1_tops_1(A_104,B_105),B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_265,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_260])).

tff(c_269,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_265])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_399,plain,(
    ! [A_116,B_117] :
      ( v3_pre_topc(k1_tops_1(A_116,B_117),A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_404,plain,
    ( v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_399])).

tff(c_408,plain,(
    v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_404])).

tff(c_119,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [A_73] : r1_tarski(A_73,A_73) ),
    inference(resolution,[status(thm)],[c_119,c_4])).

tff(c_100,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_108,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_100])).

tff(c_172,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(A_87,C_88)
      | ~ r1_tarski(B_89,C_88)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_197,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_95,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_108,c_172])).

tff(c_28,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,C_16)
      | ~ r1_tarski(B_15,C_16)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_200,plain,(
    ! [A_14,A_95] :
      ( r1_tarski(A_14,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_14,A_95)
      | ~ r1_tarski(A_95,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_197,c_28])).

tff(c_271,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_269,c_200])).

tff(c_276,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_271])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    ! [C_61] :
      ( v2_tops_1('#skF_5','#skF_4')
      | k1_xboole_0 = C_61
      | ~ v3_pre_topc(C_61,'#skF_4')
      | ~ r1_tarski(C_61,'#skF_5')
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_453,plain,(
    ! [C_120] :
      ( k1_xboole_0 = C_120
      | ~ v3_pre_topc(C_120,'#skF_4')
      | ~ r1_tarski(C_120,'#skF_5')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_80])).

tff(c_1334,plain,(
    ! [A_176] :
      ( k1_xboole_0 = A_176
      | ~ v3_pre_topc(A_176,'#skF_4')
      | ~ r1_tarski(A_176,'#skF_5')
      | ~ r1_tarski(A_176,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_453])).

tff(c_1391,plain,
    ( k1_tops_1('#skF_4','#skF_5') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_276,c_1334])).

tff(c_1441,plain,(
    k1_tops_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_408,c_1391])).

tff(c_1443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_554,c_1441])).

tff(c_1444,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2393,plain,(
    ! [A_267,B_268,C_269] :
      ( r2_hidden('#skF_2'(A_267,B_268,C_269),A_267)
      | r2_hidden('#skF_3'(A_267,B_268,C_269),C_269)
      | k4_xboole_0(A_267,B_268) = C_269 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2421,plain,(
    ! [A_267,C_269] :
      ( r2_hidden('#skF_3'(A_267,A_267,C_269),C_269)
      | k4_xboole_0(A_267,A_267) = C_269 ) ),
    inference(resolution,[status(thm)],[c_2393,c_22])).

tff(c_5695,plain,(
    ! [A_387,C_388] :
      ( r2_hidden('#skF_3'(A_387,A_387,C_388),C_388)
      | k4_xboole_0(A_387,A_387) = C_388 ) ),
    inference(resolution,[status(thm)],[c_2393,c_22])).

tff(c_1476,plain,(
    ! [D_185,B_186,A_187] :
      ( ~ r2_hidden(D_185,B_186)
      | ~ r2_hidden(D_185,k4_xboole_0(A_187,B_186)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1479,plain,(
    ! [D_185,A_19] :
      ( ~ r2_hidden(D_185,k1_xboole_0)
      | ~ r2_hidden(D_185,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1476])).

tff(c_5761,plain,(
    ! [A_394,A_395] :
      ( ~ r2_hidden('#skF_3'(A_394,A_394,k1_xboole_0),A_395)
      | k4_xboole_0(A_394,A_394) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5695,c_1479])).

tff(c_5780,plain,(
    ! [A_267] : k4_xboole_0(A_267,A_267) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2421,c_5761])).

tff(c_6057,plain,(
    ! [A_399,C_400] :
      ( r2_hidden('#skF_3'(A_399,A_399,C_400),C_400)
      | k1_xboole_0 = C_400 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5780,c_2421])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6076,plain,(
    ! [A_399,C_400,B_2] :
      ( r2_hidden('#skF_3'(A_399,A_399,C_400),B_2)
      | ~ r1_tarski(C_400,B_2)
      | k1_xboole_0 = C_400 ) ),
    inference(resolution,[status(thm)],[c_6057,c_2])).

tff(c_5783,plain,(
    ! [A_267,C_269] :
      ( r2_hidden('#skF_3'(A_267,A_267,C_269),C_269)
      | k1_xboole_0 = C_269 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5780,c_2421])).

tff(c_1445,plain,(
    v2_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v2_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1449,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_64])).

tff(c_68,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1470,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_68])).

tff(c_50,plain,(
    ! [B_44,D_50,C_48,A_36] :
      ( k1_tops_1(B_44,D_50) = D_50
      | ~ v3_pre_topc(D_50,B_44)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0(B_44)))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(B_44)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5679,plain,(
    ! [C_385,A_386] :
      ( ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386) ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_5682,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1470,c_5679])).

tff(c_5693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5682])).

tff(c_6106,plain,(
    ! [B_403,D_404] :
      ( k1_tops_1(B_403,D_404) = D_404
      | ~ v3_pre_topc(D_404,B_403)
      | ~ m1_subset_1(D_404,k1_zfmisc_1(u1_struct_0(B_403)))
      | ~ l1_pre_topc(B_403) ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6109,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1470,c_6106])).

tff(c_6119,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1449,c_6109])).

tff(c_1507,plain,(
    ! [A_196,B_197] :
      ( r2_hidden('#skF_1'(A_196,B_197),A_196)
      | r1_tarski(A_196,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1527,plain,(
    ! [A_196] : r1_tarski(A_196,A_196) ),
    inference(resolution,[status(thm)],[c_1507,c_4])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2029,plain,(
    ! [A_253,B_254,B_255] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_253,B_254),B_255),A_253)
      | r1_tarski(k4_xboole_0(A_253,B_254),B_255) ) ),
    inference(resolution,[status(thm)],[c_1507,c_12])).

tff(c_2125,plain,(
    ! [A_258,B_259] : r1_tarski(k4_xboole_0(A_258,B_259),A_258) ),
    inference(resolution,[status(thm)],[c_2029,c_4])).

tff(c_1706,plain,(
    ! [A_222,B_223] :
      ( r1_tarski(k1_tops_1(A_222,B_223),B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1708,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_6'),'#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1470,c_1706])).

tff(c_1716,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1708])).

tff(c_1738,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,'#skF_6')
      | ~ r1_tarski(A_14,k1_tops_1('#skF_4','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1716,c_28])).

tff(c_2361,plain,(
    ! [B_266] : r1_tarski(k4_xboole_0(k1_tops_1('#skF_4','#skF_6'),B_266),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2125,c_1738])).

tff(c_66,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ v2_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1447,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_66])).

tff(c_1529,plain,(
    ! [A_199,C_200,B_201] :
      ( r1_tarski(A_199,C_200)
      | ~ r1_tarski(B_201,C_200)
      | ~ r1_tarski(A_199,B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1545,plain,(
    ! [A_202] :
      ( r1_tarski(A_202,'#skF_5')
      | ~ r1_tarski(A_202,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1447,c_1529])).

tff(c_1548,plain,(
    ! [A_14,A_202] :
      ( r1_tarski(A_14,'#skF_5')
      | ~ r1_tarski(A_14,A_202)
      | ~ r1_tarski(A_202,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1545,c_28])).

tff(c_2373,plain,(
    ! [B_266] :
      ( r1_tarski(k4_xboole_0(k1_tops_1('#skF_4','#skF_6'),B_266),'#skF_5')
      | ~ r1_tarski('#skF_6','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2361,c_1548])).

tff(c_2390,plain,(
    ! [B_266] : r1_tarski(k4_xboole_0(k1_tops_1('#skF_4','#skF_6'),B_266),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_2373])).

tff(c_6131,plain,(
    ! [B_266] : r1_tarski(k4_xboole_0('#skF_6',B_266),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6119,c_2390])).

tff(c_1663,plain,(
    ! [D_216,A_217,B_218] :
      ( r2_hidden(D_216,k4_xboole_0(A_217,B_218))
      | r2_hidden(D_216,B_218)
      | ~ r2_hidden(D_216,A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9978,plain,(
    ! [D_504,B_505,A_506,B_507] :
      ( r2_hidden(D_504,B_505)
      | ~ r1_tarski(k4_xboole_0(A_506,B_507),B_505)
      | r2_hidden(D_504,B_507)
      | ~ r2_hidden(D_504,A_506) ) ),
    inference(resolution,[status(thm)],[c_1663,c_2])).

tff(c_10092,plain,(
    ! [D_504,B_266] :
      ( r2_hidden(D_504,'#skF_5')
      | r2_hidden(D_504,B_266)
      | ~ r2_hidden(D_504,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6131,c_9978])).

tff(c_10221,plain,(
    ! [D_510] :
      ( ~ r2_hidden(D_510,'#skF_6')
      | r2_hidden(D_510,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10092])).

tff(c_10307,plain,(
    ! [D_515,B_516] :
      ( r2_hidden(D_515,B_516)
      | ~ r1_tarski('#skF_5',B_516)
      | ~ r2_hidden(D_515,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10221,c_2])).

tff(c_10313,plain,(
    ! [A_267,B_516] :
      ( r2_hidden('#skF_3'(A_267,A_267,'#skF_6'),B_516)
      | ~ r1_tarski('#skF_5',B_516)
      | k1_xboole_0 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_5783,c_10307])).

tff(c_10586,plain,(
    ! [A_519,B_520] :
      ( r2_hidden('#skF_3'(A_519,A_519,'#skF_6'),B_520)
      | ~ r1_tarski('#skF_5',B_520) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1444,c_10313])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10983,plain,(
    ! [A_533,B_534,A_535] :
      ( ~ r2_hidden('#skF_3'(A_533,A_533,'#skF_6'),B_534)
      | ~ r1_tarski('#skF_5',k4_xboole_0(A_535,B_534)) ) ),
    inference(resolution,[status(thm)],[c_10586,c_10])).

tff(c_11000,plain,(
    ! [A_535,B_2] :
      ( ~ r1_tarski('#skF_5',k4_xboole_0(A_535,B_2))
      | ~ r1_tarski('#skF_6',B_2)
      | k1_xboole_0 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_6076,c_10983])).

tff(c_11121,plain,(
    ! [A_543,B_544] :
      ( ~ r1_tarski('#skF_5',k4_xboole_0(A_543,B_544))
      | ~ r1_tarski('#skF_6',B_544) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1444,c_11000])).

tff(c_11130,plain,(
    ! [A_19] :
      ( ~ r1_tarski('#skF_5',A_19)
      | ~ r1_tarski('#skF_6',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11121])).

tff(c_11131,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11130])).

tff(c_1754,plain,(
    ! [A_224,B_225] :
      ( k1_tops_1(A_224,B_225) = k1_xboole_0
      | ~ v2_tops_1(B_225,A_224)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1764,plain,
    ( k1_tops_1('#skF_4','#skF_5') = k1_xboole_0
    | ~ v2_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1754])).

tff(c_1771,plain,(
    k1_tops_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1445,c_1764])).

tff(c_3463,plain,(
    ! [A_309,B_310,C_311] :
      ( r1_tarski(k1_tops_1(A_309,B_310),k1_tops_1(A_309,C_311))
      | ~ r1_tarski(B_310,C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ l1_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3492,plain,(
    ! [B_310] :
      ( r1_tarski(k1_tops_1('#skF_4',B_310),k1_xboole_0)
      | ~ r1_tarski(B_310,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_3463])).

tff(c_29959,plain,(
    ! [B_814] :
      ( r1_tarski(k1_tops_1('#skF_4',B_814),k1_xboole_0)
      | ~ r1_tarski(B_814,'#skF_5')
      | ~ m1_subset_1(B_814,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3492])).

tff(c_29962,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_6'),k1_xboole_0)
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1470,c_29959])).

tff(c_29972,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_6119,c_29962])).

tff(c_29974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11131,c_29972])).

tff(c_29975,plain,(
    ! [A_19] : ~ r1_tarski('#skF_5',A_19) ),
    inference(splitRight,[status(thm)],[c_11130])).

tff(c_1460,plain,(
    ! [A_181,B_182] :
      ( r1_tarski(A_181,B_182)
      | ~ m1_subset_1(A_181,k1_zfmisc_1(B_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1468,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_1460])).

tff(c_29978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29975,c_1468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.20/4.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.20/4.50  
% 11.20/4.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.20/4.50  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 11.20/4.50  
% 11.20/4.50  %Foreground sorts:
% 11.20/4.50  
% 11.20/4.50  
% 11.20/4.50  %Background operators:
% 11.20/4.50  
% 11.20/4.50  
% 11.20/4.50  %Foreground operators:
% 11.20/4.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.20/4.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.20/4.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.20/4.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.20/4.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.20/4.50  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 11.20/4.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.20/4.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.20/4.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.20/4.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.20/4.50  tff('#skF_5', type, '#skF_5': $i).
% 11.20/4.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.20/4.50  tff('#skF_6', type, '#skF_6': $i).
% 11.20/4.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.20/4.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.20/4.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.20/4.50  tff('#skF_4', type, '#skF_4': $i).
% 11.20/4.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.20/4.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.20/4.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.20/4.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.20/4.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.20/4.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.20/4.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.20/4.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.20/4.50  
% 11.35/4.52  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.35/4.52  tff(f_138, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 11.35/4.52  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 11.35/4.52  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 11.35/4.52  tff(f_70, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 11.35/4.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.35/4.52  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.35/4.52  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.35/4.52  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.35/4.52  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 11.35/4.52  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 11.35/4.52  tff(c_34, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.35/4.52  tff(c_62, plain, (k1_xboole_0!='#skF_6' | ~v2_tops_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_98, plain, (~v2_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 11.35/4.52  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_542, plain, (![B_129, A_130]: (v2_tops_1(B_129, A_130) | k1_tops_1(A_130, B_129)!=k1_xboole_0 | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.35/4.52  tff(c_549, plain, (v2_tops_1('#skF_5', '#skF_4') | k1_tops_1('#skF_4', '#skF_5')!=k1_xboole_0 | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_542])).
% 11.35/4.52  tff(c_553, plain, (v2_tops_1('#skF_5', '#skF_4') | k1_tops_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_549])).
% 11.35/4.52  tff(c_554, plain, (k1_tops_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_98, c_553])).
% 11.35/4.52  tff(c_260, plain, (![A_104, B_105]: (r1_tarski(k1_tops_1(A_104, B_105), B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.35/4.52  tff(c_265, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_260])).
% 11.35/4.52  tff(c_269, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_265])).
% 11.35/4.52  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_399, plain, (![A_116, B_117]: (v3_pre_topc(k1_tops_1(A_116, B_117), A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.35/4.52  tff(c_404, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_399])).
% 11.35/4.52  tff(c_408, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_404])).
% 11.35/4.52  tff(c_119, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.35/4.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.35/4.52  tff(c_124, plain, (![A_73]: (r1_tarski(A_73, A_73))), inference(resolution, [status(thm)], [c_119, c_4])).
% 11.35/4.52  tff(c_100, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.35/4.52  tff(c_108, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_100])).
% 11.35/4.52  tff(c_172, plain, (![A_87, C_88, B_89]: (r1_tarski(A_87, C_88) | ~r1_tarski(B_89, C_88) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.35/4.52  tff(c_197, plain, (![A_95]: (r1_tarski(A_95, u1_struct_0('#skF_4')) | ~r1_tarski(A_95, '#skF_5'))), inference(resolution, [status(thm)], [c_108, c_172])).
% 11.35/4.52  tff(c_28, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, C_16) | ~r1_tarski(B_15, C_16) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.35/4.52  tff(c_200, plain, (![A_14, A_95]: (r1_tarski(A_14, u1_struct_0('#skF_4')) | ~r1_tarski(A_14, A_95) | ~r1_tarski(A_95, '#skF_5'))), inference(resolution, [status(thm)], [c_197, c_28])).
% 11.35/4.52  tff(c_271, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_269, c_200])).
% 11.35/4.52  tff(c_276, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_271])).
% 11.35/4.52  tff(c_40, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.35/4.52  tff(c_80, plain, (![C_61]: (v2_tops_1('#skF_5', '#skF_4') | k1_xboole_0=C_61 | ~v3_pre_topc(C_61, '#skF_4') | ~r1_tarski(C_61, '#skF_5') | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_453, plain, (![C_120]: (k1_xboole_0=C_120 | ~v3_pre_topc(C_120, '#skF_4') | ~r1_tarski(C_120, '#skF_5') | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_98, c_80])).
% 11.35/4.52  tff(c_1334, plain, (![A_176]: (k1_xboole_0=A_176 | ~v3_pre_topc(A_176, '#skF_4') | ~r1_tarski(A_176, '#skF_5') | ~r1_tarski(A_176, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_40, c_453])).
% 11.35/4.52  tff(c_1391, plain, (k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_276, c_1334])).
% 11.35/4.52  tff(c_1441, plain, (k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_269, c_408, c_1391])).
% 11.35/4.52  tff(c_1443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_554, c_1441])).
% 11.35/4.52  tff(c_1444, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_62])).
% 11.35/4.52  tff(c_2393, plain, (![A_267, B_268, C_269]: (r2_hidden('#skF_2'(A_267, B_268, C_269), A_267) | r2_hidden('#skF_3'(A_267, B_268, C_269), C_269) | k4_xboole_0(A_267, B_268)=C_269)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.35/4.52  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.35/4.52  tff(c_2421, plain, (![A_267, C_269]: (r2_hidden('#skF_3'(A_267, A_267, C_269), C_269) | k4_xboole_0(A_267, A_267)=C_269)), inference(resolution, [status(thm)], [c_2393, c_22])).
% 11.35/4.52  tff(c_5695, plain, (![A_387, C_388]: (r2_hidden('#skF_3'(A_387, A_387, C_388), C_388) | k4_xboole_0(A_387, A_387)=C_388)), inference(resolution, [status(thm)], [c_2393, c_22])).
% 11.35/4.52  tff(c_1476, plain, (![D_185, B_186, A_187]: (~r2_hidden(D_185, B_186) | ~r2_hidden(D_185, k4_xboole_0(A_187, B_186)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.35/4.52  tff(c_1479, plain, (![D_185, A_19]: (~r2_hidden(D_185, k1_xboole_0) | ~r2_hidden(D_185, A_19))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1476])).
% 11.35/4.52  tff(c_5761, plain, (![A_394, A_395]: (~r2_hidden('#skF_3'(A_394, A_394, k1_xboole_0), A_395) | k4_xboole_0(A_394, A_394)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5695, c_1479])).
% 11.35/4.52  tff(c_5780, plain, (![A_267]: (k4_xboole_0(A_267, A_267)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2421, c_5761])).
% 11.35/4.52  tff(c_6057, plain, (![A_399, C_400]: (r2_hidden('#skF_3'(A_399, A_399, C_400), C_400) | k1_xboole_0=C_400)), inference(demodulation, [status(thm), theory('equality')], [c_5780, c_2421])).
% 11.35/4.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.35/4.52  tff(c_6076, plain, (![A_399, C_400, B_2]: (r2_hidden('#skF_3'(A_399, A_399, C_400), B_2) | ~r1_tarski(C_400, B_2) | k1_xboole_0=C_400)), inference(resolution, [status(thm)], [c_6057, c_2])).
% 11.35/4.52  tff(c_5783, plain, (![A_267, C_269]: (r2_hidden('#skF_3'(A_267, A_267, C_269), C_269) | k1_xboole_0=C_269)), inference(demodulation, [status(thm), theory('equality')], [c_5780, c_2421])).
% 11.35/4.52  tff(c_1445, plain, (v2_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 11.35/4.52  tff(c_64, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v2_tops_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_1449, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_64])).
% 11.35/4.52  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tops_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_1470, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_68])).
% 11.35/4.52  tff(c_50, plain, (![B_44, D_50, C_48, A_36]: (k1_tops_1(B_44, D_50)=D_50 | ~v3_pre_topc(D_50, B_44) | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0(B_44))) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(B_44) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.35/4.52  tff(c_5679, plain, (![C_385, A_386]: (~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0(A_386))) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386))), inference(splitLeft, [status(thm)], [c_50])).
% 11.35/4.52  tff(c_5682, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1470, c_5679])).
% 11.35/4.52  tff(c_5693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5682])).
% 11.35/4.52  tff(c_6106, plain, (![B_403, D_404]: (k1_tops_1(B_403, D_404)=D_404 | ~v3_pre_topc(D_404, B_403) | ~m1_subset_1(D_404, k1_zfmisc_1(u1_struct_0(B_403))) | ~l1_pre_topc(B_403))), inference(splitRight, [status(thm)], [c_50])).
% 11.35/4.52  tff(c_6109, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1470, c_6106])).
% 11.35/4.52  tff(c_6119, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1449, c_6109])).
% 11.35/4.52  tff(c_1507, plain, (![A_196, B_197]: (r2_hidden('#skF_1'(A_196, B_197), A_196) | r1_tarski(A_196, B_197))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.35/4.52  tff(c_1527, plain, (![A_196]: (r1_tarski(A_196, A_196))), inference(resolution, [status(thm)], [c_1507, c_4])).
% 11.35/4.52  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.35/4.52  tff(c_2029, plain, (![A_253, B_254, B_255]: (r2_hidden('#skF_1'(k4_xboole_0(A_253, B_254), B_255), A_253) | r1_tarski(k4_xboole_0(A_253, B_254), B_255))), inference(resolution, [status(thm)], [c_1507, c_12])).
% 11.35/4.52  tff(c_2125, plain, (![A_258, B_259]: (r1_tarski(k4_xboole_0(A_258, B_259), A_258))), inference(resolution, [status(thm)], [c_2029, c_4])).
% 11.35/4.52  tff(c_1706, plain, (![A_222, B_223]: (r1_tarski(k1_tops_1(A_222, B_223), B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.35/4.52  tff(c_1708, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_6'), '#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1470, c_1706])).
% 11.35/4.52  tff(c_1716, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1708])).
% 11.35/4.52  tff(c_1738, plain, (![A_14]: (r1_tarski(A_14, '#skF_6') | ~r1_tarski(A_14, k1_tops_1('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_1716, c_28])).
% 11.35/4.52  tff(c_2361, plain, (![B_266]: (r1_tarski(k4_xboole_0(k1_tops_1('#skF_4', '#skF_6'), B_266), '#skF_6'))), inference(resolution, [status(thm)], [c_2125, c_1738])).
% 11.35/4.52  tff(c_66, plain, (r1_tarski('#skF_6', '#skF_5') | ~v2_tops_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.35/4.52  tff(c_1447, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_66])).
% 11.35/4.52  tff(c_1529, plain, (![A_199, C_200, B_201]: (r1_tarski(A_199, C_200) | ~r1_tarski(B_201, C_200) | ~r1_tarski(A_199, B_201))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.35/4.52  tff(c_1545, plain, (![A_202]: (r1_tarski(A_202, '#skF_5') | ~r1_tarski(A_202, '#skF_6'))), inference(resolution, [status(thm)], [c_1447, c_1529])).
% 11.35/4.52  tff(c_1548, plain, (![A_14, A_202]: (r1_tarski(A_14, '#skF_5') | ~r1_tarski(A_14, A_202) | ~r1_tarski(A_202, '#skF_6'))), inference(resolution, [status(thm)], [c_1545, c_28])).
% 11.35/4.52  tff(c_2373, plain, (![B_266]: (r1_tarski(k4_xboole_0(k1_tops_1('#skF_4', '#skF_6'), B_266), '#skF_5') | ~r1_tarski('#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_2361, c_1548])).
% 11.35/4.52  tff(c_2390, plain, (![B_266]: (r1_tarski(k4_xboole_0(k1_tops_1('#skF_4', '#skF_6'), B_266), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_2373])).
% 11.35/4.52  tff(c_6131, plain, (![B_266]: (r1_tarski(k4_xboole_0('#skF_6', B_266), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6119, c_2390])).
% 11.35/4.52  tff(c_1663, plain, (![D_216, A_217, B_218]: (r2_hidden(D_216, k4_xboole_0(A_217, B_218)) | r2_hidden(D_216, B_218) | ~r2_hidden(D_216, A_217))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.35/4.52  tff(c_9978, plain, (![D_504, B_505, A_506, B_507]: (r2_hidden(D_504, B_505) | ~r1_tarski(k4_xboole_0(A_506, B_507), B_505) | r2_hidden(D_504, B_507) | ~r2_hidden(D_504, A_506))), inference(resolution, [status(thm)], [c_1663, c_2])).
% 11.35/4.52  tff(c_10092, plain, (![D_504, B_266]: (r2_hidden(D_504, '#skF_5') | r2_hidden(D_504, B_266) | ~r2_hidden(D_504, '#skF_6'))), inference(resolution, [status(thm)], [c_6131, c_9978])).
% 11.35/4.52  tff(c_10221, plain, (![D_510]: (~r2_hidden(D_510, '#skF_6') | r2_hidden(D_510, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_10092])).
% 11.35/4.52  tff(c_10307, plain, (![D_515, B_516]: (r2_hidden(D_515, B_516) | ~r1_tarski('#skF_5', B_516) | ~r2_hidden(D_515, '#skF_6'))), inference(resolution, [status(thm)], [c_10221, c_2])).
% 11.35/4.52  tff(c_10313, plain, (![A_267, B_516]: (r2_hidden('#skF_3'(A_267, A_267, '#skF_6'), B_516) | ~r1_tarski('#skF_5', B_516) | k1_xboole_0='#skF_6')), inference(resolution, [status(thm)], [c_5783, c_10307])).
% 11.35/4.52  tff(c_10586, plain, (![A_519, B_520]: (r2_hidden('#skF_3'(A_519, A_519, '#skF_6'), B_520) | ~r1_tarski('#skF_5', B_520))), inference(negUnitSimplification, [status(thm)], [c_1444, c_10313])).
% 11.35/4.52  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.35/4.52  tff(c_10983, plain, (![A_533, B_534, A_535]: (~r2_hidden('#skF_3'(A_533, A_533, '#skF_6'), B_534) | ~r1_tarski('#skF_5', k4_xboole_0(A_535, B_534)))), inference(resolution, [status(thm)], [c_10586, c_10])).
% 11.35/4.52  tff(c_11000, plain, (![A_535, B_2]: (~r1_tarski('#skF_5', k4_xboole_0(A_535, B_2)) | ~r1_tarski('#skF_6', B_2) | k1_xboole_0='#skF_6')), inference(resolution, [status(thm)], [c_6076, c_10983])).
% 11.35/4.52  tff(c_11121, plain, (![A_543, B_544]: (~r1_tarski('#skF_5', k4_xboole_0(A_543, B_544)) | ~r1_tarski('#skF_6', B_544))), inference(negUnitSimplification, [status(thm)], [c_1444, c_11000])).
% 11.35/4.52  tff(c_11130, plain, (![A_19]: (~r1_tarski('#skF_5', A_19) | ~r1_tarski('#skF_6', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_11121])).
% 11.35/4.52  tff(c_11131, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11130])).
% 11.35/4.52  tff(c_1754, plain, (![A_224, B_225]: (k1_tops_1(A_224, B_225)=k1_xboole_0 | ~v2_tops_1(B_225, A_224) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.35/4.52  tff(c_1764, plain, (k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0 | ~v2_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1754])).
% 11.35/4.52  tff(c_1771, plain, (k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1445, c_1764])).
% 11.35/4.52  tff(c_3463, plain, (![A_309, B_310, C_311]: (r1_tarski(k1_tops_1(A_309, B_310), k1_tops_1(A_309, C_311)) | ~r1_tarski(B_310, C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(u1_struct_0(A_309))) | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0(A_309))) | ~l1_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.35/4.52  tff(c_3492, plain, (![B_310]: (r1_tarski(k1_tops_1('#skF_4', B_310), k1_xboole_0) | ~r1_tarski(B_310, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1771, c_3463])).
% 11.35/4.52  tff(c_29959, plain, (![B_814]: (r1_tarski(k1_tops_1('#skF_4', B_814), k1_xboole_0) | ~r1_tarski(B_814, '#skF_5') | ~m1_subset_1(B_814, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3492])).
% 11.35/4.52  tff(c_29962, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_6'), k1_xboole_0) | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1470, c_29959])).
% 11.35/4.52  tff(c_29972, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_6119, c_29962])).
% 11.35/4.52  tff(c_29974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11131, c_29972])).
% 11.35/4.52  tff(c_29975, plain, (![A_19]: (~r1_tarski('#skF_5', A_19))), inference(splitRight, [status(thm)], [c_11130])).
% 11.35/4.52  tff(c_1460, plain, (![A_181, B_182]: (r1_tarski(A_181, B_182) | ~m1_subset_1(A_181, k1_zfmisc_1(B_182)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.35/4.52  tff(c_1468, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_1460])).
% 11.35/4.52  tff(c_29978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29975, c_1468])).
% 11.35/4.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.35/4.52  
% 11.35/4.52  Inference rules
% 11.35/4.52  ----------------------
% 11.35/4.52  #Ref     : 0
% 11.35/4.52  #Sup     : 6912
% 11.35/4.52  #Fact    : 8
% 11.35/4.52  #Define  : 0
% 11.35/4.52  #Split   : 16
% 11.35/4.52  #Chain   : 0
% 11.35/4.52  #Close   : 0
% 11.35/4.52  
% 11.35/4.52  Ordering : KBO
% 11.35/4.52  
% 11.35/4.52  Simplification rules
% 11.35/4.52  ----------------------
% 11.35/4.52  #Subsume      : 2055
% 11.35/4.52  #Demod        : 6896
% 11.35/4.52  #Tautology    : 3203
% 11.35/4.52  #SimpNegUnit  : 85
% 11.35/4.53  #BackRed      : 59
% 11.35/4.53  
% 11.35/4.53  #Partial instantiations: 0
% 11.35/4.53  #Strategies tried      : 1
% 11.35/4.53  
% 11.35/4.53  Timing (in seconds)
% 11.35/4.53  ----------------------
% 11.35/4.53  Preprocessing        : 0.36
% 11.35/4.53  Parsing              : 0.18
% 11.35/4.53  CNF conversion       : 0.03
% 11.35/4.53  Main loop            : 3.39
% 11.35/4.53  Inferencing          : 0.77
% 11.35/4.53  Reduction            : 1.44
% 11.35/4.53  Demodulation         : 1.13
% 11.35/4.53  BG Simplification    : 0.09
% 11.35/4.53  Subsumption          : 0.90
% 11.35/4.53  Abstraction          : 0.12
% 11.35/4.53  MUC search           : 0.00
% 11.35/4.53  Cooper               : 0.00
% 11.35/4.53  Total                : 3.79
% 11.35/4.53  Index Insertion      : 0.00
% 11.35/4.53  Index Deletion       : 0.00
% 11.35/4.53  Index Matching       : 0.00
% 11.35/4.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
