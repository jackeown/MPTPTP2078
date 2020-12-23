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
% DateTime   : Thu Dec  3 10:21:51 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 134 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 393 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_56,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_328,plain,(
    ! [B_75,A_76] :
      ( v2_tops_1(B_75,A_76)
      | k1_tops_1(A_76,B_75) != k1_xboole_0
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_335,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_328])).

tff(c_343,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_335])).

tff(c_344,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_343])).

tff(c_139,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_144,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_151,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_144])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_285,plain,(
    ! [A_71,B_72] :
      ( v3_pre_topc(k1_tops_1(A_71,B_72),A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_290,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_285])).

tff(c_297,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_290])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_85,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_50,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_69,c_85])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_416,plain,(
    ! [A_83,A_84] :
      ( r1_tarski(A_83,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_83,A_84)
      | ~ r1_tarski(A_84,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_424,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_151,c_416])).

tff(c_442,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_424])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [C_34] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_34
      | ~ v3_pre_topc(C_34,'#skF_1')
      | ~ r1_tarski(C_34,'#skF_2')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_306,plain,(
    ! [C_74] :
      ( k1_xboole_0 = C_74
      | ~ v3_pre_topc(C_74,'#skF_1')
      | ~ r1_tarski(C_74,'#skF_2')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52])).

tff(c_531,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ v3_pre_topc(A_90,'#skF_1')
      | ~ r1_tarski(A_90,'#skF_2')
      | ~ r1_tarski(A_90,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_306])).

tff(c_537,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_442,c_531])).

tff(c_562,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_297,c_537])).

tff(c_564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_562])).

tff(c_565,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_566,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_570,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_36])).

tff(c_38,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_568,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_38])).

tff(c_40,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_587,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_40])).

tff(c_1042,plain,(
    ! [A_133,B_134] :
      ( k1_tops_1(A_133,B_134) = k1_xboole_0
      | ~ v2_tops_1(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1052,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1042])).

tff(c_1064,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_566,c_1052])).

tff(c_1164,plain,(
    ! [B_142,A_143,C_144] :
      ( r1_tarski(B_142,k1_tops_1(A_143,C_144))
      | ~ r1_tarski(B_142,C_144)
      | ~ v3_pre_topc(B_142,A_143)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1171,plain,(
    ! [B_142] :
      ( r1_tarski(B_142,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_142,'#skF_2')
      | ~ v3_pre_topc(B_142,'#skF_1')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1164])).

tff(c_1227,plain,(
    ! [B_148] :
      ( r1_tarski(B_148,k1_xboole_0)
      | ~ r1_tarski(B_148,'#skF_2')
      | ~ v3_pre_topc(B_148,'#skF_1')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1064,c_1171])).

tff(c_1230,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_587,c_1227])).

tff(c_1244,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_568,c_1230])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_572,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(A_93,B_94)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_584,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_10,c_572])).

tff(c_592,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_605,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_584,c_592])).

tff(c_1264,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1244,c_605])).

tff(c_1281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_1264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:07:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  
% 3.23/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.47  
% 3.23/1.47  %Foreground sorts:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Background operators:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Foreground operators:
% 3.23/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.23/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.23/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.23/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.47  
% 3.32/1.49  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.32/1.49  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.32/1.49  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.32/1.49  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.32/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.49  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.49  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.32/1.49  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.32/1.49  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.32/1.49  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_56, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 3.32/1.49  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_328, plain, (![B_75, A_76]: (v2_tops_1(B_75, A_76) | k1_tops_1(A_76, B_75)!=k1_xboole_0 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.49  tff(c_335, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_328])).
% 3.32/1.49  tff(c_343, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_335])).
% 3.32/1.49  tff(c_344, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_343])).
% 3.32/1.49  tff(c_139, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.49  tff(c_144, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_139])).
% 3.32/1.49  tff(c_151, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_144])).
% 3.32/1.49  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_285, plain, (![A_71, B_72]: (v3_pre_topc(k1_tops_1(A_71, B_72), A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.32/1.49  tff(c_290, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_285])).
% 3.32/1.49  tff(c_297, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_290])).
% 3.32/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.49  tff(c_58, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.49  tff(c_69, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_58])).
% 3.32/1.49  tff(c_85, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.49  tff(c_119, plain, (![A_50]: (r1_tarski(A_50, u1_struct_0('#skF_1')) | ~r1_tarski(A_50, '#skF_2'))), inference(resolution, [status(thm)], [c_69, c_85])).
% 3.32/1.49  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.49  tff(c_416, plain, (![A_83, A_84]: (r1_tarski(A_83, u1_struct_0('#skF_1')) | ~r1_tarski(A_83, A_84) | ~r1_tarski(A_84, '#skF_2'))), inference(resolution, [status(thm)], [c_119, c_8])).
% 3.32/1.49  tff(c_424, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_151, c_416])).
% 3.32/1.49  tff(c_442, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_424])).
% 3.32/1.49  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.49  tff(c_52, plain, (![C_34]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_34 | ~v3_pre_topc(C_34, '#skF_1') | ~r1_tarski(C_34, '#skF_2') | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_306, plain, (![C_74]: (k1_xboole_0=C_74 | ~v3_pre_topc(C_74, '#skF_1') | ~r1_tarski(C_74, '#skF_2') | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_52])).
% 3.32/1.49  tff(c_531, plain, (![A_90]: (k1_xboole_0=A_90 | ~v3_pre_topc(A_90, '#skF_1') | ~r1_tarski(A_90, '#skF_2') | ~r1_tarski(A_90, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_306])).
% 3.32/1.49  tff(c_537, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_442, c_531])).
% 3.32/1.49  tff(c_562, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151, c_297, c_537])).
% 3.32/1.49  tff(c_564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_562])).
% 3.32/1.49  tff(c_565, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.32/1.49  tff(c_566, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 3.32/1.49  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_570, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_36])).
% 3.32/1.49  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_568, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_38])).
% 3.32/1.49  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_587, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_40])).
% 3.32/1.49  tff(c_1042, plain, (![A_133, B_134]: (k1_tops_1(A_133, B_134)=k1_xboole_0 | ~v2_tops_1(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.49  tff(c_1052, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1042])).
% 3.32/1.49  tff(c_1064, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_566, c_1052])).
% 3.32/1.49  tff(c_1164, plain, (![B_142, A_143, C_144]: (r1_tarski(B_142, k1_tops_1(A_143, C_144)) | ~r1_tarski(B_142, C_144) | ~v3_pre_topc(B_142, A_143) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.32/1.49  tff(c_1171, plain, (![B_142]: (r1_tarski(B_142, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_142, '#skF_2') | ~v3_pre_topc(B_142, '#skF_1') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1164])).
% 3.32/1.49  tff(c_1227, plain, (![B_148]: (r1_tarski(B_148, k1_xboole_0) | ~r1_tarski(B_148, '#skF_2') | ~v3_pre_topc(B_148, '#skF_1') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1064, c_1171])).
% 3.32/1.49  tff(c_1230, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_587, c_1227])).
% 3.32/1.49  tff(c_1244, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_570, c_568, c_1230])).
% 3.32/1.49  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.49  tff(c_572, plain, (![A_93, B_94]: (r1_tarski(A_93, B_94) | ~m1_subset_1(A_93, k1_zfmisc_1(B_94)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.49  tff(c_584, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_10, c_572])).
% 3.32/1.49  tff(c_592, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.49  tff(c_605, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_584, c_592])).
% 3.32/1.49  tff(c_1264, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1244, c_605])).
% 3.32/1.49  tff(c_1281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_1264])).
% 3.32/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.49  
% 3.32/1.49  Inference rules
% 3.32/1.49  ----------------------
% 3.32/1.49  #Ref     : 0
% 3.32/1.49  #Sup     : 269
% 3.32/1.49  #Fact    : 0
% 3.32/1.49  #Define  : 0
% 3.32/1.49  #Split   : 14
% 3.32/1.49  #Chain   : 0
% 3.32/1.49  #Close   : 0
% 3.32/1.49  
% 3.32/1.49  Ordering : KBO
% 3.32/1.49  
% 3.32/1.49  Simplification rules
% 3.32/1.49  ----------------------
% 3.32/1.49  #Subsume      : 110
% 3.32/1.49  #Demod        : 138
% 3.32/1.49  #Tautology    : 59
% 3.32/1.49  #SimpNegUnit  : 5
% 3.32/1.49  #BackRed      : 2
% 3.32/1.49  
% 3.32/1.49  #Partial instantiations: 0
% 3.32/1.49  #Strategies tried      : 1
% 3.32/1.49  
% 3.32/1.49  Timing (in seconds)
% 3.32/1.49  ----------------------
% 3.32/1.49  Preprocessing        : 0.31
% 3.32/1.49  Parsing              : 0.16
% 3.32/1.49  CNF conversion       : 0.02
% 3.32/1.49  Main loop            : 0.42
% 3.32/1.49  Inferencing          : 0.15
% 3.32/1.49  Reduction            : 0.14
% 3.32/1.49  Demodulation         : 0.09
% 3.32/1.49  BG Simplification    : 0.02
% 3.32/1.49  Subsumption          : 0.09
% 3.32/1.49  Abstraction          : 0.02
% 3.32/1.49  MUC search           : 0.00
% 3.32/1.49  Cooper               : 0.00
% 3.32/1.49  Total                : 0.76
% 3.32/1.49  Index Insertion      : 0.00
% 3.32/1.49  Index Deletion       : 0.00
% 3.32/1.49  Index Matching       : 0.00
% 3.32/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
