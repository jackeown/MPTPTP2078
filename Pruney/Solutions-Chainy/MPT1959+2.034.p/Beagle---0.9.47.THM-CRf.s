%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:02 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 261 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  191 ( 979 expanded)
%              Number of equality atoms :   18 (  68 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_120,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_188,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_1'(A_85,B_86),A_85)
      | B_86 = A_85
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    ! [A_25,B_27] :
      ( r2_lattice3(A_25,k1_xboole_0,B_27)
      | ~ m1_subset_1(B_27,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_206,plain,(
    ! [A_25,B_86] :
      ( r2_lattice3(A_25,k1_xboole_0,'#skF_1'(u1_struct_0(A_25),B_86))
      | ~ l1_orders_2(A_25)
      | u1_struct_0(A_25) = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_25))) ) ),
    inference(resolution,[status(thm)],[c_188,c_30])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_86,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_92,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_89])).

tff(c_68,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_99,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68])).

tff(c_100,plain,(
    ! [B_62,A_63] :
      ( v1_subset_1(B_62,A_63)
      | B_62 = A_63
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_103,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_106,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_103])).

tff(c_76,plain,(
    ! [A_57] :
      ( k1_yellow_0(A_57,k1_xboole_0) = k3_yellow_0(A_57)
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    k1_yellow_0('#skF_5',k1_xboole_0) = k3_yellow_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_93,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k1_yellow_0(A_60,B_61),u1_struct_0(A_60))
      | ~ l1_orders_2(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_96,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_93])).

tff(c_98,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_96])).

tff(c_108,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_98])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_108])).

tff(c_113,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_116,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k1_yellow_0(A_64,B_65),u1_struct_0(A_64))
      | ~ l1_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_116])).

tff(c_121,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_119])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_26,plain,(
    ! [A_24] :
      ( r1_yellow_0(A_24,k1_xboole_0)
      | ~ l1_orders_2(A_24)
      | ~ v1_yellow_0(A_24)
      | ~ v5_orders_2(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_665,plain,(
    ! [A_202,B_203,D_204] :
      ( r1_orders_2(A_202,k1_yellow_0(A_202,B_203),D_204)
      | ~ r2_lattice3(A_202,B_203,D_204)
      | ~ m1_subset_1(D_204,u1_struct_0(A_202))
      | ~ r1_yellow_0(A_202,B_203)
      | ~ m1_subset_1(k1_yellow_0(A_202,B_203),u1_struct_0(A_202))
      | ~ l1_orders_2(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_672,plain,(
    ! [D_204] :
      ( r1_orders_2('#skF_5',k1_yellow_0('#skF_5',k1_xboole_0),D_204)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_204)
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_665])).

tff(c_678,plain,(
    ! [D_204] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),D_204)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_204)
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_121,c_80,c_672])).

tff(c_679,plain,(
    ~ r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_678])).

tff(c_682,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v1_yellow_0('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_679])).

tff(c_685,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_682])).

tff(c_687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_685])).

tff(c_688,plain,(
    ! [D_204] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),D_204)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_204)
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_723,plain,(
    ! [D_214,B_215,A_216,C_217] :
      ( r2_hidden(D_214,B_215)
      | ~ r1_orders_2(A_216,C_217,D_214)
      | ~ r2_hidden(C_217,B_215)
      | ~ m1_subset_1(D_214,u1_struct_0(A_216))
      | ~ m1_subset_1(C_217,u1_struct_0(A_216))
      | ~ v13_waybel_0(B_215,A_216)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_orders_2(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_727,plain,(
    ! [D_204,B_215] :
      ( r2_hidden(D_204,B_215)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_215)
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_215,'#skF_5')
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_204)
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_688,c_723])).

tff(c_745,plain,(
    ! [D_220,B_221] :
      ( r2_hidden(D_220,B_221)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_221)
      | ~ v13_waybel_0(B_221,'#skF_5')
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_220)
      | ~ m1_subset_1(D_220,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_121,c_727])).

tff(c_750,plain,(
    ! [D_220] :
      ( r2_hidden(D_220,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_220)
      | ~ m1_subset_1(D_220,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_745])).

tff(c_755,plain,(
    ! [D_222] :
      ( r2_hidden(D_222,'#skF_6')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_222)
      | ~ m1_subset_1(D_222,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_113,c_750])).

tff(c_830,plain,(
    ! [B_224] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_224),'#skF_6')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_5'),B_224))
      | u1_struct_0('#skF_5') = B_224
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_755])).

tff(c_834,plain,(
    ! [B_86] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_86),'#skF_6')
      | ~ l1_orders_2('#skF_5')
      | u1_struct_0('#skF_5') = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_206,c_830])).

tff(c_857,plain,(
    ! [B_227] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_227),'#skF_6')
      | u1_struct_0('#skF_5') = B_227
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_834])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_865,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_857,c_2])).

tff(c_870,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_865])).

tff(c_112,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_881,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_112])).

tff(c_882,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_48])).

tff(c_46,plain,(
    ! [B_54] :
      ( ~ v1_subset_1(B_54,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_982,plain,(
    ~ v1_subset_1('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_882,c_46])).

tff(c_990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:25:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.55  
% 3.35/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.55  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.60/1.55  
% 3.60/1.55  %Foreground sorts:
% 3.60/1.55  
% 3.60/1.55  
% 3.60/1.55  %Background operators:
% 3.60/1.55  
% 3.60/1.55  
% 3.60/1.55  %Foreground operators:
% 3.60/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.60/1.55  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.60/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.60/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.55  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.60/1.55  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.60/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.55  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.60/1.55  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.60/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.60/1.55  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.60/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.60/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.60/1.55  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 3.60/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.60/1.55  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.60/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.60/1.55  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.60/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.60/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.60/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.55  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.60/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.60/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.60/1.55  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 3.60/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.55  
% 3.61/1.57  tff(f_149, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 3.61/1.57  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 3.61/1.57  tff(f_94, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.61/1.57  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.61/1.57  tff(f_120, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.61/1.57  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.61/1.57  tff(f_72, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 3.61/1.57  tff(f_85, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 3.61/1.57  tff(f_68, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 3.61/1.57  tff(f_113, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 3.61/1.57  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_56, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_188, plain, (![A_85, B_86]: (m1_subset_1('#skF_1'(A_85, B_86), A_85) | B_86=A_85 | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.61/1.57  tff(c_30, plain, (![A_25, B_27]: (r2_lattice3(A_25, k1_xboole_0, B_27) | ~m1_subset_1(B_27, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.61/1.57  tff(c_206, plain, (![A_25, B_86]: (r2_lattice3(A_25, k1_xboole_0, '#skF_1'(u1_struct_0(A_25), B_86)) | ~l1_orders_2(A_25) | u1_struct_0(A_25)=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_25))))), inference(resolution, [status(thm)], [c_188, c_30])).
% 3.61/1.57  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.61/1.57  tff(c_50, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_54, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.61/1.57  tff(c_74, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_86, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 3.61/1.57  tff(c_89, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_6, c_86])).
% 3.61/1.57  tff(c_92, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_89])).
% 3.61/1.57  tff(c_68, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_99, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_86, c_68])).
% 3.61/1.57  tff(c_100, plain, (![B_62, A_63]: (v1_subset_1(B_62, A_63) | B_62=A_63 | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.61/1.57  tff(c_103, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_48, c_100])).
% 3.61/1.57  tff(c_106, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_99, c_103])).
% 3.61/1.57  tff(c_76, plain, (![A_57]: (k1_yellow_0(A_57, k1_xboole_0)=k3_yellow_0(A_57) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.61/1.57  tff(c_80, plain, (k1_yellow_0('#skF_5', k1_xboole_0)=k3_yellow_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_76])).
% 3.61/1.57  tff(c_93, plain, (![A_60, B_61]: (m1_subset_1(k1_yellow_0(A_60, B_61), u1_struct_0(A_60)) | ~l1_orders_2(A_60))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.57  tff(c_96, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_80, c_93])).
% 3.61/1.57  tff(c_98, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_96])).
% 3.61/1.57  tff(c_108, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_98])).
% 3.61/1.57  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_108])).
% 3.61/1.57  tff(c_113, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 3.61/1.57  tff(c_116, plain, (![A_64, B_65]: (m1_subset_1(k1_yellow_0(A_64, B_65), u1_struct_0(A_64)) | ~l1_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.57  tff(c_119, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_80, c_116])).
% 3.61/1.57  tff(c_121, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_119])).
% 3.61/1.57  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_60, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_58, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.61/1.57  tff(c_26, plain, (![A_24]: (r1_yellow_0(A_24, k1_xboole_0) | ~l1_orders_2(A_24) | ~v1_yellow_0(A_24) | ~v5_orders_2(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.57  tff(c_665, plain, (![A_202, B_203, D_204]: (r1_orders_2(A_202, k1_yellow_0(A_202, B_203), D_204) | ~r2_lattice3(A_202, B_203, D_204) | ~m1_subset_1(D_204, u1_struct_0(A_202)) | ~r1_yellow_0(A_202, B_203) | ~m1_subset_1(k1_yellow_0(A_202, B_203), u1_struct_0(A_202)) | ~l1_orders_2(A_202))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.61/1.57  tff(c_672, plain, (![D_204]: (r1_orders_2('#skF_5', k1_yellow_0('#skF_5', k1_xboole_0), D_204) | ~r2_lattice3('#skF_5', k1_xboole_0, D_204) | ~m1_subset_1(D_204, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_665])).
% 3.61/1.57  tff(c_678, plain, (![D_204]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), D_204) | ~r2_lattice3('#skF_5', k1_xboole_0, D_204) | ~m1_subset_1(D_204, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_121, c_80, c_672])).
% 3.61/1.57  tff(c_679, plain, (~r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_678])).
% 3.61/1.57  tff(c_682, plain, (~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_679])).
% 3.61/1.57  tff(c_685, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_682])).
% 3.61/1.57  tff(c_687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_685])).
% 3.61/1.57  tff(c_688, plain, (![D_204]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), D_204) | ~r2_lattice3('#skF_5', k1_xboole_0, D_204) | ~m1_subset_1(D_204, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_678])).
% 3.61/1.57  tff(c_723, plain, (![D_214, B_215, A_216, C_217]: (r2_hidden(D_214, B_215) | ~r1_orders_2(A_216, C_217, D_214) | ~r2_hidden(C_217, B_215) | ~m1_subset_1(D_214, u1_struct_0(A_216)) | ~m1_subset_1(C_217, u1_struct_0(A_216)) | ~v13_waybel_0(B_215, A_216) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_orders_2(A_216))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.61/1.57  tff(c_727, plain, (![D_204, B_215]: (r2_hidden(D_204, B_215) | ~r2_hidden(k3_yellow_0('#skF_5'), B_215) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_215, '#skF_5') | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~r2_lattice3('#skF_5', k1_xboole_0, D_204) | ~m1_subset_1(D_204, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_688, c_723])).
% 3.61/1.57  tff(c_745, plain, (![D_220, B_221]: (r2_hidden(D_220, B_221) | ~r2_hidden(k3_yellow_0('#skF_5'), B_221) | ~v13_waybel_0(B_221, '#skF_5') | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_lattice3('#skF_5', k1_xboole_0, D_220) | ~m1_subset_1(D_220, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_121, c_727])).
% 3.61/1.57  tff(c_750, plain, (![D_220]: (r2_hidden(D_220, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~r2_lattice3('#skF_5', k1_xboole_0, D_220) | ~m1_subset_1(D_220, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_745])).
% 3.61/1.57  tff(c_755, plain, (![D_222]: (r2_hidden(D_222, '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, D_222) | ~m1_subset_1(D_222, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_113, c_750])).
% 3.61/1.57  tff(c_830, plain, (![B_224]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_224), '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_5'), B_224)) | u1_struct_0('#skF_5')=B_224 | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_755])).
% 3.61/1.57  tff(c_834, plain, (![B_86]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_86), '#skF_6') | ~l1_orders_2('#skF_5') | u1_struct_0('#skF_5')=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_206, c_830])).
% 3.61/1.57  tff(c_857, plain, (![B_227]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_227), '#skF_6') | u1_struct_0('#skF_5')=B_227 | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_834])).
% 3.61/1.57  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.61/1.57  tff(c_865, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_857, c_2])).
% 3.61/1.57  tff(c_870, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_865])).
% 3.61/1.57  tff(c_112, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 3.61/1.57  tff(c_881, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_870, c_112])).
% 3.61/1.57  tff(c_882, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_48])).
% 3.61/1.57  tff(c_46, plain, (![B_54]: (~v1_subset_1(B_54, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.61/1.57  tff(c_982, plain, (~v1_subset_1('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_882, c_46])).
% 3.61/1.57  tff(c_990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_881, c_982])).
% 3.61/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.57  
% 3.61/1.57  Inference rules
% 3.61/1.57  ----------------------
% 3.61/1.57  #Ref     : 0
% 3.61/1.57  #Sup     : 157
% 3.61/1.57  #Fact    : 0
% 3.61/1.57  #Define  : 0
% 3.61/1.57  #Split   : 5
% 3.61/1.57  #Chain   : 0
% 3.61/1.57  #Close   : 0
% 3.61/1.57  
% 3.61/1.57  Ordering : KBO
% 3.61/1.57  
% 3.61/1.57  Simplification rules
% 3.61/1.57  ----------------------
% 3.61/1.57  #Subsume      : 12
% 3.61/1.57  #Demod        : 215
% 3.61/1.57  #Tautology    : 49
% 3.61/1.57  #SimpNegUnit  : 11
% 3.61/1.57  #BackRed      : 28
% 3.61/1.57  
% 3.61/1.57  #Partial instantiations: 0
% 3.61/1.57  #Strategies tried      : 1
% 3.61/1.57  
% 3.61/1.57  Timing (in seconds)
% 3.61/1.57  ----------------------
% 3.61/1.57  Preprocessing        : 0.35
% 3.61/1.57  Parsing              : 0.18
% 3.61/1.57  CNF conversion       : 0.03
% 3.61/1.57  Main loop            : 0.45
% 3.61/1.57  Inferencing          : 0.17
% 3.61/1.57  Reduction            : 0.14
% 3.61/1.57  Demodulation         : 0.09
% 3.61/1.57  BG Simplification    : 0.03
% 3.61/1.57  Subsumption          : 0.08
% 3.61/1.57  Abstraction          : 0.02
% 3.61/1.57  MUC search           : 0.00
% 3.61/1.57  Cooper               : 0.00
% 3.61/1.57  Total                : 0.84
% 3.61/1.57  Index Insertion      : 0.00
% 3.61/1.57  Index Deletion       : 0.00
% 3.61/1.57  Index Matching       : 0.00
% 3.61/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
