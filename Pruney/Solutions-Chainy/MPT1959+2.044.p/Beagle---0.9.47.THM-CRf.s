%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:03 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 441 expanded)
%              Number of leaves         :   36 ( 169 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 (1515 expanded)
%              Number of equality atoms :   14 ( 141 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_48,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_orders_2(A_43) ) ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_77,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_40])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1('#skF_1'(A_3,B_4),A_3)
      | B_4 = A_3
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_140,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_104,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_60])).

tff(c_105,plain,(
    ~ v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_66,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_137,plain,
    ( v1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_66])).

tff(c_138,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_137])).

tff(c_146,plain,
    ( ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_140,c_138])).

tff(c_150,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_146])).

tff(c_156,plain,(
    ! [B_56,A_57] :
      ( v1_subset_1(B_56,A_57)
      | B_56 = A_57
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_163,plain,
    ( v1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | k2_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_78,c_156])).

tff(c_167,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_163])).

tff(c_83,plain,(
    ! [A_44] :
      ( m1_subset_1(k3_yellow_0(A_44),u1_struct_0(A_44))
      | ~ l1_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_86,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_83])).

tff(c_88,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_86])).

tff(c_172,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_88])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_172])).

tff(c_177,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_22,plain,(
    ! [A_10,B_12] :
      ( r1_orders_2(A_10,k3_yellow_0(A_10),B_12)
      | ~ m1_subset_1(B_12,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10)
      | ~ v1_yellow_0(A_10)
      | ~ v5_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_440,plain,(
    ! [D_116,B_117,A_118,C_119] :
      ( r2_hidden(D_116,B_117)
      | ~ r1_orders_2(A_118,C_119,D_116)
      | ~ r2_hidden(C_119,B_117)
      | ~ m1_subset_1(D_116,u1_struct_0(A_118))
      | ~ m1_subset_1(C_119,u1_struct_0(A_118))
      | ~ v13_waybel_0(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_474,plain,(
    ! [B_126,B_127,A_128] :
      ( r2_hidden(B_126,B_127)
      | ~ r2_hidden(k3_yellow_0(A_128),B_127)
      | ~ m1_subset_1(k3_yellow_0(A_128),u1_struct_0(A_128))
      | ~ v13_waybel_0(B_127,A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_126,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v1_yellow_0(A_128)
      | ~ v5_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_22,c_440])).

tff(c_481,plain,(
    ! [B_126,B_127] :
      ( r2_hidden(B_126,B_127)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_127)
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),k2_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_127,'#skF_4')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_yellow_0('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_474])).

tff(c_485,plain,(
    ! [B_126,B_127] :
      ( r2_hidden(B_126,B_127)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_127)
      | ~ v13_waybel_0(B_127,'#skF_4')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_126,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_77,c_77,c_88,c_481])).

tff(c_487,plain,(
    ! [B_129,B_130] :
      ( r2_hidden(B_129,B_130)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_130)
      | ~ v13_waybel_0(B_130,'#skF_4')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_129,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_485])).

tff(c_495,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,'#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
      | ~ v13_waybel_0('#skF_5','#skF_4')
      | ~ m1_subset_1(B_129,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_78,c_487])).

tff(c_501,plain,(
    ! [B_131] :
      ( r2_hidden(B_131,'#skF_5')
      | ~ m1_subset_1(B_131,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_177,c_495])).

tff(c_562,plain,(
    ! [B_136] :
      ( r2_hidden('#skF_1'(k2_struct_0('#skF_4'),B_136),'#skF_5')
      | k2_struct_0('#skF_4') = B_136
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_501])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | B_4 = A_3
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_566,plain,
    ( k2_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_562,c_10])).

tff(c_572,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_566])).

tff(c_193,plain,(
    ! [A_61] :
      ( ~ v1_subset_1(k2_struct_0(A_61),u1_struct_0(A_61))
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_196,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_193])).

tff(c_198,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_201,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_201])).

tff(c_206,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_588,plain,(
    ~ v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_572,c_206])).

tff(c_178,plain,(
    v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_590,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_178])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  
% 2.83/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.83/1.41  
% 2.83/1.41  %Foreground sorts:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Background operators:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Foreground operators:
% 2.83/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.83/1.41  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.83/1.41  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.83/1.41  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.83/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.83/1.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.83/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.41  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.83/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.83/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.41  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 2.83/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.41  
% 2.83/1.42  tff(f_133, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 2.83/1.42  tff(f_60, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.83/1.42  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.83/1.42  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.83/1.42  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.83/1.42  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.83/1.42  tff(f_64, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 2.83/1.42  tff(f_78, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 2.83/1.42  tff(f_97, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 2.83/1.42  tff(f_56, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.83/1.42  tff(c_48, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.83/1.42  tff(c_68, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.42  tff(c_73, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_orders_2(A_43))), inference(resolution, [status(thm)], [c_18, c_68])).
% 2.83/1.42  tff(c_77, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_73])).
% 2.83/1.42  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_40])).
% 2.83/1.42  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1('#skF_1'(A_3, B_4), A_3) | B_4=A_3 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.42  tff(c_42, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_46, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_140, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.42  tff(c_60, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_104, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_60])).
% 2.83/1.42  tff(c_105, plain, (~v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_104])).
% 2.83/1.42  tff(c_66, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_137, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_66])).
% 2.83/1.42  tff(c_138, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_105, c_137])).
% 2.83/1.42  tff(c_146, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_140, c_138])).
% 2.83/1.42  tff(c_150, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_146])).
% 2.83/1.42  tff(c_156, plain, (![B_56, A_57]: (v1_subset_1(B_56, A_57) | B_56=A_57 | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.42  tff(c_163, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4')) | k2_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_78, c_156])).
% 2.83/1.42  tff(c_167, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_105, c_163])).
% 2.83/1.42  tff(c_83, plain, (![A_44]: (m1_subset_1(k3_yellow_0(A_44), u1_struct_0(A_44)) | ~l1_orders_2(A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.42  tff(c_86, plain, (m1_subset_1(k3_yellow_0('#skF_4'), k2_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77, c_83])).
% 2.83/1.42  tff(c_88, plain, (m1_subset_1(k3_yellow_0('#skF_4'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_86])).
% 2.83/1.42  tff(c_172, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_88])).
% 2.83/1.42  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_172])).
% 2.83/1.42  tff(c_177, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_104])).
% 2.83/1.42  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_52, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_50, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.83/1.42  tff(c_22, plain, (![A_10, B_12]: (r1_orders_2(A_10, k3_yellow_0(A_10), B_12) | ~m1_subset_1(B_12, u1_struct_0(A_10)) | ~l1_orders_2(A_10) | ~v1_yellow_0(A_10) | ~v5_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.42  tff(c_440, plain, (![D_116, B_117, A_118, C_119]: (r2_hidden(D_116, B_117) | ~r1_orders_2(A_118, C_119, D_116) | ~r2_hidden(C_119, B_117) | ~m1_subset_1(D_116, u1_struct_0(A_118)) | ~m1_subset_1(C_119, u1_struct_0(A_118)) | ~v13_waybel_0(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.42  tff(c_474, plain, (![B_126, B_127, A_128]: (r2_hidden(B_126, B_127) | ~r2_hidden(k3_yellow_0(A_128), B_127) | ~m1_subset_1(k3_yellow_0(A_128), u1_struct_0(A_128)) | ~v13_waybel_0(B_127, A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_126, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v1_yellow_0(A_128) | ~v5_orders_2(A_128) | v2_struct_0(A_128))), inference(resolution, [status(thm)], [c_22, c_440])).
% 2.83/1.43  tff(c_481, plain, (![B_126, B_127]: (r2_hidden(B_126, B_127) | ~r2_hidden(k3_yellow_0('#skF_4'), B_127) | ~m1_subset_1(k3_yellow_0('#skF_4'), k2_struct_0('#skF_4')) | ~v13_waybel_0(B_127, '#skF_4') | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_126, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_474])).
% 2.83/1.43  tff(c_485, plain, (![B_126, B_127]: (r2_hidden(B_126, B_127) | ~r2_hidden(k3_yellow_0('#skF_4'), B_127) | ~v13_waybel_0(B_127, '#skF_4') | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_126, k2_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_77, c_77, c_88, c_481])).
% 2.83/1.43  tff(c_487, plain, (![B_129, B_130]: (r2_hidden(B_129, B_130) | ~r2_hidden(k3_yellow_0('#skF_4'), B_130) | ~v13_waybel_0(B_130, '#skF_4') | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_129, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_485])).
% 2.83/1.43  tff(c_495, plain, (![B_129]: (r2_hidden(B_129, '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | ~m1_subset_1(B_129, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_78, c_487])).
% 2.83/1.43  tff(c_501, plain, (![B_131]: (r2_hidden(B_131, '#skF_5') | ~m1_subset_1(B_131, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_177, c_495])).
% 2.83/1.43  tff(c_562, plain, (![B_136]: (r2_hidden('#skF_1'(k2_struct_0('#skF_4'), B_136), '#skF_5') | k2_struct_0('#skF_4')=B_136 | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_12, c_501])).
% 2.83/1.43  tff(c_10, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | B_4=A_3 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.43  tff(c_566, plain, (k2_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_562, c_10])).
% 2.83/1.43  tff(c_572, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_566])).
% 2.83/1.43  tff(c_193, plain, (![A_61]: (~v1_subset_1(k2_struct_0(A_61), u1_struct_0(A_61)) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.43  tff(c_196, plain, (~v1_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77, c_193])).
% 2.83/1.43  tff(c_198, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_196])).
% 2.83/1.43  tff(c_201, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_18, c_198])).
% 2.83/1.43  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_201])).
% 2.83/1.43  tff(c_206, plain, (~v1_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_196])).
% 2.83/1.43  tff(c_588, plain, (~v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_572, c_206])).
% 2.83/1.43  tff(c_178, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_104])).
% 2.83/1.43  tff(c_590, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_178])).
% 2.83/1.43  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_590])).
% 2.83/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  Inference rules
% 2.83/1.43  ----------------------
% 2.83/1.43  #Ref     : 0
% 2.83/1.43  #Sup     : 97
% 2.83/1.43  #Fact    : 0
% 2.83/1.43  #Define  : 0
% 2.83/1.43  #Split   : 5
% 2.83/1.43  #Chain   : 0
% 2.83/1.43  #Close   : 0
% 2.83/1.43  
% 2.83/1.43  Ordering : KBO
% 2.83/1.43  
% 2.83/1.43  Simplification rules
% 3.11/1.43  ----------------------
% 3.11/1.43  #Subsume      : 23
% 3.11/1.43  #Demod        : 111
% 3.11/1.43  #Tautology    : 24
% 3.11/1.43  #SimpNegUnit  : 10
% 3.11/1.43  #BackRed      : 27
% 3.11/1.43  
% 3.11/1.43  #Partial instantiations: 0
% 3.11/1.43  #Strategies tried      : 1
% 3.11/1.43  
% 3.11/1.43  Timing (in seconds)
% 3.11/1.43  ----------------------
% 3.11/1.43  Preprocessing        : 0.32
% 3.11/1.43  Parsing              : 0.17
% 3.11/1.43  CNF conversion       : 0.02
% 3.11/1.43  Main loop            : 0.34
% 3.11/1.43  Inferencing          : 0.12
% 3.11/1.43  Reduction            : 0.10
% 3.11/1.43  Demodulation         : 0.07
% 3.11/1.43  BG Simplification    : 0.02
% 3.11/1.43  Subsumption          : 0.06
% 3.11/1.43  Abstraction          : 0.02
% 3.11/1.43  MUC search           : 0.00
% 3.11/1.43  Cooper               : 0.00
% 3.11/1.43  Total                : 0.69
% 3.11/1.43  Index Insertion      : 0.00
% 3.11/1.43  Index Deletion       : 0.00
% 3.11/1.43  Index Matching       : 0.00
% 3.11/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
