%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:30 EST 2020

% Result     : Theorem 15.78s
% Output     : CNFRefutation 15.88s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 176 expanded)
%              Number of leaves         :   39 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 357 expanded)
%              Number of equality atoms :   19 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_108,axiom,(
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

tff(f_122,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_44,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_81,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_87,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_91,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_46])).

tff(c_97,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_97])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_479,plain,(
    ! [B_113,A_114] :
      ( v4_pre_topc(B_113,A_114)
      | ~ v1_xboole_0(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_482,plain,(
    ! [B_113] :
      ( v4_pre_topc(B_113,'#skF_2')
      | ~ v1_xboole_0(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_479])).

tff(c_555,plain,(
    ! [B_119] :
      ( v4_pre_topc(B_119,'#skF_2')
      | ~ v1_xboole_0(B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_482])).

tff(c_566,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_2')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_555])).

tff(c_579,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_566])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_281,plain,(
    ! [A_93,B_94,C_95] :
      ( k7_subset_1(A_93,B_94,C_95) = k4_xboole_0(B_94,C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_297,plain,(
    ! [A_8,C_95] : k7_subset_1(A_8,A_8,C_95) = k4_xboole_0(A_8,C_95) ),
    inference(resolution,[status(thm)],[c_53,c_281])).

tff(c_584,plain,(
    ! [A_120,B_121] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_120),k2_struct_0(A_120),B_121),A_120)
      | ~ v4_pre_topc(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_587,plain,(
    ! [B_121] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_121),'#skF_2')
      | ~ v4_pre_topc(B_121,'#skF_2')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_584])).

tff(c_728,plain,(
    ! [B_130] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'),B_130),'#skF_2')
      | ~ v4_pre_topc(B_130,'#skF_2')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_91,c_297,c_587])).

tff(c_732,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_2')
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_728])).

tff(c_734,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_579,c_732])).

tff(c_38,plain,(
    ! [B_36,D_42,C_40,A_28] :
      ( k1_tops_1(B_36,D_42) = D_42
      | ~ v3_pre_topc(D_42,B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1252,plain,(
    ! [C_163,A_164] :
      ( ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_1275,plain,(
    ! [A_165] :
      ( ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165) ) ),
    inference(resolution,[status(thm)],[c_18,c_1252])).

tff(c_1278,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1275])).

tff(c_1282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1278])).

tff(c_1509,plain,(
    ! [B_176,D_177] :
      ( k1_tops_1(B_176,D_177) = D_177
      | ~ v3_pre_topc(D_177,B_176)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(u1_struct_0(B_176)))
      | ~ l1_pre_topc(B_176) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1512,plain,(
    ! [D_177] :
      ( k1_tops_1('#skF_2',D_177) = D_177
      | ~ v3_pre_topc(D_177,'#skF_2')
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_1509])).

tff(c_1587,plain,(
    ! [D_182] :
      ( k1_tops_1('#skF_2',D_182) = D_182
      | ~ v3_pre_topc(D_182,'#skF_2')
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1512])).

tff(c_1606,plain,
    ( k1_tops_1('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_1587])).

tff(c_1613,plain,(
    k1_tops_1('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_1606])).

tff(c_1620,plain,(
    ! [C_183,A_184,B_185] :
      ( m2_connsp_2(C_183,A_184,B_185)
      | ~ r1_tarski(B_185,k1_tops_1(A_184,C_183))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1622,plain,(
    ! [B_185] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_185)
      | ~ r1_tarski(B_185,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_1620])).

tff(c_43159,plain,(
    ! [B_1059] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_1059)
      | ~ r1_tarski(B_1059,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1059,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_91,c_53,c_91,c_1622])).

tff(c_43162,plain,
    ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_43159])).

tff(c_43181,plain,(
    m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_43162])).

tff(c_43183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_43181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.78/8.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.78/8.50  
% 15.78/8.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.78/8.51  %$ m2_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 15.78/8.51  
% 15.78/8.51  %Foreground sorts:
% 15.78/8.51  
% 15.78/8.51  
% 15.78/8.51  %Background operators:
% 15.78/8.51  
% 15.78/8.51  
% 15.78/8.51  %Foreground operators:
% 15.78/8.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.78/8.51  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 15.78/8.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.78/8.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.78/8.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.78/8.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.78/8.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.78/8.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.78/8.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.78/8.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 15.78/8.51  tff('#skF_2', type, '#skF_2': $i).
% 15.78/8.51  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 15.78/8.51  tff('#skF_3', type, '#skF_3': $i).
% 15.78/8.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.78/8.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.78/8.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 15.78/8.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.78/8.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.78/8.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.78/8.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.78/8.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 15.78/8.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.78/8.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.78/8.51  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 15.78/8.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.78/8.51  
% 15.88/8.52  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 15.88/8.52  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 15.88/8.52  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 15.88/8.52  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.88/8.52  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 15.88/8.52  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 15.88/8.52  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 15.88/8.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.88/8.52  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 15.88/8.52  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 15.88/8.52  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 15.88/8.52  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 15.88/8.52  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 15.88/8.52  tff(f_122, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 15.88/8.52  tff(c_44, plain, (~m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.88/8.52  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.88/8.52  tff(c_34, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.88/8.52  tff(c_81, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.88/8.52  tff(c_87, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_34, c_81])).
% 15.88/8.52  tff(c_91, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_87])).
% 15.88/8.52  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.88/8.52  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_46])).
% 15.88/8.52  tff(c_97, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.88/8.52  tff(c_114, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_92, c_97])).
% 15.88/8.52  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.88/8.52  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.88/8.52  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.88/8.52  tff(c_53, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 15.88/8.52  tff(c_18, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.88/8.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 15.88/8.52  tff(c_479, plain, (![B_113, A_114]: (v4_pre_topc(B_113, A_114) | ~v1_xboole_0(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.88/8.52  tff(c_482, plain, (![B_113]: (v4_pre_topc(B_113, '#skF_2') | ~v1_xboole_0(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_479])).
% 15.88/8.52  tff(c_555, plain, (![B_119]: (v4_pre_topc(B_119, '#skF_2') | ~v1_xboole_0(B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_482])).
% 15.88/8.52  tff(c_566, plain, (v4_pre_topc(k1_xboole_0, '#skF_2') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_555])).
% 15.88/8.52  tff(c_579, plain, (v4_pre_topc(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_566])).
% 15.88/8.52  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.88/8.52  tff(c_281, plain, (![A_93, B_94, C_95]: (k7_subset_1(A_93, B_94, C_95)=k4_xboole_0(B_94, C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.88/8.52  tff(c_297, plain, (![A_8, C_95]: (k7_subset_1(A_8, A_8, C_95)=k4_xboole_0(A_8, C_95))), inference(resolution, [status(thm)], [c_53, c_281])).
% 15.88/8.52  tff(c_584, plain, (![A_120, B_121]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_120), k2_struct_0(A_120), B_121), A_120) | ~v4_pre_topc(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_83])).
% 15.88/8.52  tff(c_587, plain, (![B_121]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_121), '#skF_2') | ~v4_pre_topc(B_121, '#skF_2') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_584])).
% 15.88/8.52  tff(c_728, plain, (![B_130]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'), B_130), '#skF_2') | ~v4_pre_topc(B_130, '#skF_2') | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_91, c_297, c_587])).
% 15.88/8.52  tff(c_732, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v4_pre_topc(k1_xboole_0, '#skF_2') | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8, c_728])).
% 15.88/8.52  tff(c_734, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_579, c_732])).
% 15.88/8.52  tff(c_38, plain, (![B_36, D_42, C_40, A_28]: (k1_tops_1(B_36, D_42)=D_42 | ~v3_pre_topc(D_42, B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(B_36))) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.88/8.52  tff(c_1252, plain, (![C_163, A_164]: (~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164))), inference(splitLeft, [status(thm)], [c_38])).
% 15.88/8.52  tff(c_1275, plain, (![A_165]: (~l1_pre_topc(A_165) | ~v2_pre_topc(A_165))), inference(resolution, [status(thm)], [c_18, c_1252])).
% 15.88/8.52  tff(c_1278, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1275])).
% 15.88/8.52  tff(c_1282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1278])).
% 15.88/8.52  tff(c_1509, plain, (![B_176, D_177]: (k1_tops_1(B_176, D_177)=D_177 | ~v3_pre_topc(D_177, B_176) | ~m1_subset_1(D_177, k1_zfmisc_1(u1_struct_0(B_176))) | ~l1_pre_topc(B_176))), inference(splitRight, [status(thm)], [c_38])).
% 15.88/8.52  tff(c_1512, plain, (![D_177]: (k1_tops_1('#skF_2', D_177)=D_177 | ~v3_pre_topc(D_177, '#skF_2') | ~m1_subset_1(D_177, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_1509])).
% 15.88/8.52  tff(c_1587, plain, (![D_182]: (k1_tops_1('#skF_2', D_182)=D_182 | ~v3_pre_topc(D_182, '#skF_2') | ~m1_subset_1(D_182, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1512])).
% 15.88/8.52  tff(c_1606, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_53, c_1587])).
% 15.88/8.52  tff(c_1613, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_734, c_1606])).
% 15.88/8.52  tff(c_1620, plain, (![C_183, A_184, B_185]: (m2_connsp_2(C_183, A_184, B_185) | ~r1_tarski(B_185, k1_tops_1(A_184, C_183)) | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0(A_184))) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184))), inference(cnfTransformation, [status(thm)], [f_122])).
% 15.88/8.52  tff(c_1622, plain, (![B_185]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_185) | ~r1_tarski(B_185, k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1613, c_1620])).
% 15.88/8.52  tff(c_43159, plain, (![B_1059]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_1059) | ~r1_tarski(B_1059, k2_struct_0('#skF_2')) | ~m1_subset_1(B_1059, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_91, c_53, c_91, c_1622])).
% 15.88/8.52  tff(c_43162, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_92, c_43159])).
% 15.88/8.52  tff(c_43181, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_43162])).
% 15.88/8.52  tff(c_43183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_43181])).
% 15.88/8.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.88/8.52  
% 15.88/8.52  Inference rules
% 15.88/8.52  ----------------------
% 15.88/8.52  #Ref     : 0
% 15.88/8.52  #Sup     : 9107
% 15.88/8.52  #Fact    : 0
% 15.88/8.52  #Define  : 0
% 15.88/8.52  #Split   : 22
% 15.88/8.52  #Chain   : 0
% 15.88/8.52  #Close   : 0
% 15.88/8.52  
% 15.88/8.52  Ordering : KBO
% 15.88/8.52  
% 15.88/8.52  Simplification rules
% 15.88/8.52  ----------------------
% 15.88/8.52  #Subsume      : 292
% 15.88/8.52  #Demod        : 4225
% 15.88/8.52  #Tautology    : 3687
% 15.88/8.52  #SimpNegUnit  : 14
% 15.88/8.52  #BackRed      : 2
% 15.88/8.52  
% 15.88/8.52  #Partial instantiations: 0
% 15.88/8.52  #Strategies tried      : 1
% 15.88/8.52  
% 15.88/8.52  Timing (in seconds)
% 15.88/8.52  ----------------------
% 15.88/8.53  Preprocessing        : 0.35
% 15.88/8.53  Parsing              : 0.19
% 15.88/8.53  CNF conversion       : 0.03
% 15.88/8.53  Main loop            : 7.39
% 15.88/8.53  Inferencing          : 1.15
% 15.88/8.53  Reduction            : 3.33
% 15.88/8.53  Demodulation         : 2.81
% 15.88/8.53  BG Simplification    : 0.15
% 15.88/8.53  Subsumption          : 2.27
% 15.88/8.53  Abstraction          : 0.25
% 15.88/8.53  MUC search           : 0.00
% 15.88/8.53  Cooper               : 0.00
% 15.88/8.53  Total                : 7.77
% 15.88/8.53  Index Insertion      : 0.00
% 15.88/8.53  Index Deletion       : 0.00
% 15.88/8.53  Index Matching       : 0.00
% 15.88/8.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
