%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:29 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 260 expanded)
%              Number of leaves         :   49 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  172 ( 676 expanded)
%              Number of equality atoms :   40 ( 138 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_166,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_125,axiom,(
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

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_94,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_146,axiom,(
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_79,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_83,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_114,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(u1_struct_0(A_56))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_117,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_114])).

tff(c_119,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117])).

tff(c_120,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_119])).

tff(c_52,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_50,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_443,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_446,plain,(
    ! [C_102] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',C_102) = k4_xboole_0('#skF_6',C_102) ),
    inference(resolution,[status(thm)],[c_46,c_443])).

tff(c_696,plain,(
    ! [A_125,B_126] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125))),B_126,k1_tarski(k1_xboole_0)) = k2_yellow19(A_125,k3_yellow19(A_125,k2_struct_0(A_125),B_126))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125)))))
      | ~ v13_waybel_0(B_126,k3_yellow_1(k2_struct_0(A_125)))
      | ~ v2_waybel_0(B_126,k3_yellow_1(k2_struct_0(A_125)))
      | v1_xboole_0(B_126)
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_698,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_696])).

tff(c_701,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_48,c_446,c_698])).

tff(c_702,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_701])).

tff(c_44,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_737,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_44])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_222,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),B_75)
      | r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [B_75,A_74] :
      ( ~ v1_xboole_0(B_75)
      | r1_xboole_0(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_32,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_4'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_241,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_267,plain,(
    ! [A_83,B_84] :
      ( ~ r1_xboole_0(A_83,B_84)
      | k3_xboole_0(A_83,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_284,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ v1_xboole_0(B_86) ) ),
    inference(resolution,[status(thm)],[c_234,c_267])).

tff(c_307,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_318,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = k4_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_18])).

tff(c_323,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_318])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),k1_tarski(B_21))
      | B_21 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_121,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,B_58)
      | ~ r1_xboole_0(k1_tarski(A_57),B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden(A_20,k1_tarski(B_21))
      | B_21 = A_20 ) ),
    inference(resolution,[status(thm)],[c_24,c_121])).

tff(c_766,plain,(
    ! [A_130,B_131] :
      ( '#skF_2'(A_130,k1_tarski(B_131)) = B_131
      | r1_xboole_0(A_130,k1_tarski(B_131)) ) ),
    inference(resolution,[status(thm)],[c_222,c_125])).

tff(c_261,plain,(
    ! [A_78,B_79] :
      ( ~ r1_xboole_0(A_78,B_79)
      | k3_xboole_0(A_78,B_79) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_1736,plain,(
    ! [A_187,B_188] :
      ( k3_xboole_0(A_187,k1_tarski(B_188)) = k1_xboole_0
      | '#skF_2'(A_187,k1_tarski(B_188)) = B_188 ) ),
    inference(resolution,[status(thm)],[c_766,c_261])).

tff(c_1800,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(A_187,k1_tarski(B_188)) = k5_xboole_0(A_187,k1_xboole_0)
      | '#skF_2'(A_187,k1_tarski(B_188)) = B_188 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1736,c_18])).

tff(c_1926,plain,(
    ! [A_194,B_195] :
      ( k4_xboole_0(A_194,k1_tarski(B_195)) = A_194
      | '#skF_2'(A_194,k1_tarski(B_195)) = B_195 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_1800])).

tff(c_1976,plain,(
    '#skF_2'('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_737])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1998,plain,
    ( r2_hidden(k1_xboole_0,'#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1976,c_12])).

tff(c_2045,plain,(
    r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1998])).

tff(c_2052,plain,(
    k3_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2045,c_261])).

tff(c_2092,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_18])).

tff(c_2124,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_2092])).

tff(c_2126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_737,c_2124])).

tff(c_2127,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1998])).

tff(c_42,plain,(
    ! [C_41,B_39,A_35] :
      ( ~ v1_xboole_0(C_41)
      | ~ r2_hidden(C_41,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v2_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v1_subset_1(B_39,u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0(B_39)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2171,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_2127,c_42])).

tff(c_2181,plain,(
    ! [A_35] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2171])).

tff(c_2301,plain,(
    ! [A_203] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_203))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_203))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_203))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_203)))
      | v1_xboole_0(A_203) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2181])).

tff(c_2304,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_2301])).

tff(c_2307,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_2304])).

tff(c_2309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_2307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.66  
% 3.77/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.66  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 3.77/1.66  
% 3.77/1.66  %Foreground sorts:
% 3.77/1.66  
% 3.77/1.66  
% 3.77/1.66  %Background operators:
% 3.77/1.66  
% 3.77/1.66  
% 3.77/1.66  %Foreground operators:
% 3.77/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.77/1.66  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.77/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.66  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.77/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.66  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.77/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.77/1.66  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.77/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.77/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.66  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.77/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.77/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.77/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.77/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.77/1.66  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.77/1.66  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.77/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.77/1.66  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.77/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.77/1.66  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.77/1.66  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.77/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.77/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.77/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.77/1.66  
% 3.77/1.68  tff(f_166, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.77/1.68  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.77/1.68  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.77/1.68  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.77/1.68  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.77/1.68  tff(f_125, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 3.77/1.68  tff(f_68, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.77/1.68  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.77/1.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.77/1.68  tff(f_94, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.77/1.68  tff(f_64, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.77/1.68  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.77/1.68  tff(f_78, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.77/1.68  tff(f_73, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.77/1.68  tff(f_146, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 3.77/1.68  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_56, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_79, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.77/1.68  tff(c_83, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_79])).
% 3.77/1.68  tff(c_114, plain, (![A_56]: (~v1_xboole_0(u1_struct_0(A_56)) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.77/1.68  tff(c_117, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_83, c_114])).
% 3.77/1.68  tff(c_119, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117])).
% 3.77/1.68  tff(c_120, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_119])).
% 3.77/1.68  tff(c_52, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_50, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_48, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_54, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.68  tff(c_443, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.77/1.68  tff(c_446, plain, (![C_102]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', C_102)=k4_xboole_0('#skF_6', C_102))), inference(resolution, [status(thm)], [c_46, c_443])).
% 3.77/1.68  tff(c_696, plain, (![A_125, B_126]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125))), B_126, k1_tarski(k1_xboole_0))=k2_yellow19(A_125, k3_yellow19(A_125, k2_struct_0(A_125), B_126)) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125))))) | ~v13_waybel_0(B_126, k3_yellow_1(k2_struct_0(A_125))) | ~v2_waybel_0(B_126, k3_yellow_1(k2_struct_0(A_125))) | v1_xboole_0(B_126) | ~l1_struct_0(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.77/1.68  tff(c_698, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_696])).
% 3.77/1.68  tff(c_701, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_48, c_446, c_698])).
% 3.77/1.68  tff(c_702, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_701])).
% 3.77/1.68  tff(c_44, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.77/1.68  tff(c_737, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_702, c_44])).
% 3.77/1.68  tff(c_20, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.77/1.68  tff(c_222, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), B_75) | r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.77/1.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.68  tff(c_234, plain, (![B_75, A_74]: (~v1_xboole_0(B_75) | r1_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_222, c_2])).
% 3.77/1.68  tff(c_32, plain, (![A_27]: (r2_hidden('#skF_4'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.77/1.68  tff(c_241, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.77/1.68  tff(c_267, plain, (![A_83, B_84]: (~r1_xboole_0(A_83, B_84) | k3_xboole_0(A_83, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_241])).
% 3.77/1.68  tff(c_284, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=k1_xboole_0 | ~v1_xboole_0(B_86))), inference(resolution, [status(thm)], [c_234, c_267])).
% 3.77/1.68  tff(c_307, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_284])).
% 3.77/1.68  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.77/1.68  tff(c_318, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=k4_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_307, c_18])).
% 3.77/1.68  tff(c_323, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_318])).
% 3.77/1.68  tff(c_24, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), k1_tarski(B_21)) | B_21=A_20)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.77/1.68  tff(c_121, plain, (![A_57, B_58]: (~r2_hidden(A_57, B_58) | ~r1_xboole_0(k1_tarski(A_57), B_58))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.77/1.68  tff(c_125, plain, (![A_20, B_21]: (~r2_hidden(A_20, k1_tarski(B_21)) | B_21=A_20)), inference(resolution, [status(thm)], [c_24, c_121])).
% 3.77/1.68  tff(c_766, plain, (![A_130, B_131]: ('#skF_2'(A_130, k1_tarski(B_131))=B_131 | r1_xboole_0(A_130, k1_tarski(B_131)))), inference(resolution, [status(thm)], [c_222, c_125])).
% 3.77/1.68  tff(c_261, plain, (![A_78, B_79]: (~r1_xboole_0(A_78, B_79) | k3_xboole_0(A_78, B_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_241])).
% 3.77/1.68  tff(c_1736, plain, (![A_187, B_188]: (k3_xboole_0(A_187, k1_tarski(B_188))=k1_xboole_0 | '#skF_2'(A_187, k1_tarski(B_188))=B_188)), inference(resolution, [status(thm)], [c_766, c_261])).
% 3.77/1.68  tff(c_1800, plain, (![A_187, B_188]: (k4_xboole_0(A_187, k1_tarski(B_188))=k5_xboole_0(A_187, k1_xboole_0) | '#skF_2'(A_187, k1_tarski(B_188))=B_188)), inference(superposition, [status(thm), theory('equality')], [c_1736, c_18])).
% 3.77/1.68  tff(c_1926, plain, (![A_194, B_195]: (k4_xboole_0(A_194, k1_tarski(B_195))=A_194 | '#skF_2'(A_194, k1_tarski(B_195))=B_195)), inference(demodulation, [status(thm), theory('equality')], [c_323, c_1800])).
% 3.77/1.68  tff(c_1976, plain, ('#skF_2'('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1926, c_737])).
% 3.77/1.68  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.77/1.68  tff(c_1998, plain, (r2_hidden(k1_xboole_0, '#skF_6') | r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1976, c_12])).
% 3.77/1.68  tff(c_2045, plain, (r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1998])).
% 3.77/1.68  tff(c_2052, plain, (k3_xboole_0('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_2045, c_261])).
% 3.77/1.68  tff(c_2092, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2052, c_18])).
% 3.77/1.68  tff(c_2124, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_2092])).
% 3.77/1.68  tff(c_2126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_737, c_2124])).
% 3.77/1.68  tff(c_2127, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_1998])).
% 3.77/1.68  tff(c_42, plain, (![C_41, B_39, A_35]: (~v1_xboole_0(C_41) | ~r2_hidden(C_41, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0(B_39, k3_yellow_1(A_35)) | ~v2_waybel_0(B_39, k3_yellow_1(A_35)) | ~v1_subset_1(B_39, u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0(B_39) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.77/1.68  tff(c_2171, plain, (![A_35]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_2127, c_42])).
% 3.77/1.68  tff(c_2181, plain, (![A_35]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2171])).
% 3.77/1.68  tff(c_2301, plain, (![A_203]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_203)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_203)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_203)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_203))) | v1_xboole_0(A_203))), inference(negUnitSimplification, [status(thm)], [c_54, c_2181])).
% 3.77/1.68  tff(c_2304, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_2301])).
% 3.77/1.68  tff(c_2307, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_2304])).
% 3.77/1.68  tff(c_2309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_2307])).
% 3.77/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.68  
% 3.77/1.68  Inference rules
% 3.77/1.68  ----------------------
% 3.77/1.68  #Ref     : 0
% 3.77/1.68  #Sup     : 525
% 3.77/1.68  #Fact    : 0
% 3.77/1.68  #Define  : 0
% 3.77/1.68  #Split   : 5
% 3.77/1.68  #Chain   : 0
% 3.77/1.68  #Close   : 0
% 3.77/1.68  
% 3.77/1.68  Ordering : KBO
% 3.77/1.68  
% 3.77/1.68  Simplification rules
% 3.77/1.68  ----------------------
% 3.77/1.68  #Subsume      : 116
% 3.77/1.68  #Demod        : 177
% 3.77/1.68  #Tautology    : 285
% 3.77/1.68  #SimpNegUnit  : 25
% 3.77/1.68  #BackRed      : 1
% 3.77/1.68  
% 3.77/1.68  #Partial instantiations: 0
% 3.77/1.68  #Strategies tried      : 1
% 3.77/1.68  
% 3.77/1.68  Timing (in seconds)
% 3.77/1.68  ----------------------
% 3.77/1.68  Preprocessing        : 0.33
% 3.77/1.68  Parsing              : 0.18
% 3.77/1.68  CNF conversion       : 0.02
% 3.77/1.68  Main loop            : 0.53
% 3.77/1.68  Inferencing          : 0.20
% 3.77/1.68  Reduction            : 0.16
% 3.77/1.68  Demodulation         : 0.11
% 3.77/1.68  BG Simplification    : 0.03
% 3.77/1.68  Subsumption          : 0.10
% 3.77/1.68  Abstraction          : 0.03
% 3.77/1.68  MUC search           : 0.00
% 3.77/1.68  Cooper               : 0.00
% 3.77/1.68  Total                : 0.90
% 3.77/1.68  Index Insertion      : 0.00
% 3.77/1.68  Index Deletion       : 0.00
% 3.77/1.68  Index Matching       : 0.00
% 3.77/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
