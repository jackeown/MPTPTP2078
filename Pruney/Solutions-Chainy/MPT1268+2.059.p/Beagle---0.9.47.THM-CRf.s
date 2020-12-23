%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:54 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 120 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 352 expanded)
%              Number of equality atoms :   20 (  49 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_98,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_276,plain,(
    ! [B_66,A_67] :
      ( v2_tops_1(B_66,A_67)
      | k1_tops_1(A_67,B_66) != k1_xboole_0
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_283,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_276])).

tff(c_287,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_283])).

tff(c_288,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_287])).

tff(c_79,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tops_1(A_44,B_45),B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_88,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_84])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_335,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc(k1_tops_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_340,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_335])).

tff(c_344,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_340])).

tff(c_57,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_66,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_39,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_65,c_66])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [C_31] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_31
      | ~ v3_pre_topc(C_31,'#skF_1')
      | ~ r1_tarski(C_31,'#skF_2')
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_191,plain,(
    ! [C_57] :
      ( k1_xboole_0 = C_57
      | ~ v3_pre_topc(C_57,'#skF_1')
      | ~ r1_tarski(C_57,'#skF_2')
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46])).

tff(c_219,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v3_pre_topc(A_61,'#skF_1')
      | ~ r1_tarski(A_61,'#skF_2')
      | ~ r1_tarski(A_61,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_191])).

tff(c_240,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v3_pre_topc(A_39,'#skF_1')
      | ~ r1_tarski(A_39,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_71,c_219])).

tff(c_347,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_344,c_240])).

tff(c_350,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_347])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_350])).

tff(c_353,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_354,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_358,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_30])).

tff(c_32,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_356,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_32])).

tff(c_34,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_367,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_34])).

tff(c_1083,plain,(
    ! [A_134,B_135] :
      ( k1_tops_1(A_134,B_135) = k1_xboole_0
      | ~ v2_tops_1(B_135,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1093,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1083])).

tff(c_1101,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_354,c_1093])).

tff(c_1392,plain,(
    ! [B_153,A_154,C_155] :
      ( r1_tarski(B_153,k1_tops_1(A_154,C_155))
      | ~ r1_tarski(B_153,C_155)
      | ~ v3_pre_topc(B_153,A_154)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1399,plain,(
    ! [B_153] :
      ( r1_tarski(B_153,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_153,'#skF_2')
      | ~ v3_pre_topc(B_153,'#skF_1')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_1392])).

tff(c_1460,plain,(
    ! [B_160] :
      ( r1_tarski(B_160,k1_xboole_0)
      | ~ r1_tarski(B_160,'#skF_2')
      | ~ v3_pre_topc(B_160,'#skF_1')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1101,c_1399])).

tff(c_1467,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_367,c_1460])).

tff(c_1474,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_356,c_1467])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_382,plain,(
    ! [A_80,C_81,B_82] :
      ( r1_tarski(A_80,C_81)
      | ~ r1_tarski(B_82,C_81)
      | ~ r1_tarski(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_394,plain,(
    ! [A_80,A_4] :
      ( r1_tarski(A_80,A_4)
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_382])).

tff(c_1501,plain,(
    ! [A_161] : r1_tarski('#skF_3',A_161) ),
    inference(resolution,[status(thm)],[c_1474,c_394])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1539,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1501,c_6])).

tff(c_1562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_1539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:42:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.52  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.52  
% 3.21/1.52  %Foreground sorts:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Background operators:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Foreground operators:
% 3.21/1.52  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.52  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.21/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.21/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.52  
% 3.51/1.53  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.51/1.53  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.51/1.53  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.51/1.53  tff(f_49, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.51/1.53  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.51/1.53  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.51/1.53  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.51/1.53  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.51/1.53  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.51/1.53  tff(c_28, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_48, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 3.51/1.53  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_276, plain, (![B_66, A_67]: (v2_tops_1(B_66, A_67) | k1_tops_1(A_67, B_66)!=k1_xboole_0 | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.51/1.53  tff(c_283, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_276])).
% 3.51/1.53  tff(c_287, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_283])).
% 3.51/1.53  tff(c_288, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_287])).
% 3.51/1.53  tff(c_79, plain, (![A_44, B_45]: (r1_tarski(k1_tops_1(A_44, B_45), B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.51/1.53  tff(c_84, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_79])).
% 3.51/1.53  tff(c_88, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_84])).
% 3.51/1.53  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_335, plain, (![A_72, B_73]: (v3_pre_topc(k1_tops_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.51/1.53  tff(c_340, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_335])).
% 3.51/1.53  tff(c_344, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_340])).
% 3.51/1.53  tff(c_57, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.51/1.53  tff(c_65, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_57])).
% 3.51/1.53  tff(c_66, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.51/1.53  tff(c_71, plain, (![A_39]: (r1_tarski(A_39, u1_struct_0('#skF_1')) | ~r1_tarski(A_39, '#skF_2'))), inference(resolution, [status(thm)], [c_65, c_66])).
% 3.51/1.53  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.51/1.53  tff(c_46, plain, (![C_31]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_31 | ~v3_pre_topc(C_31, '#skF_1') | ~r1_tarski(C_31, '#skF_2') | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_191, plain, (![C_57]: (k1_xboole_0=C_57 | ~v3_pre_topc(C_57, '#skF_1') | ~r1_tarski(C_57, '#skF_2') | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_46])).
% 3.51/1.53  tff(c_219, plain, (![A_61]: (k1_xboole_0=A_61 | ~v3_pre_topc(A_61, '#skF_1') | ~r1_tarski(A_61, '#skF_2') | ~r1_tarski(A_61, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_191])).
% 3.51/1.53  tff(c_240, plain, (![A_39]: (k1_xboole_0=A_39 | ~v3_pre_topc(A_39, '#skF_1') | ~r1_tarski(A_39, '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_219])).
% 3.51/1.53  tff(c_347, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_344, c_240])).
% 3.51/1.53  tff(c_350, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_347])).
% 3.51/1.53  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_350])).
% 3.51/1.53  tff(c_353, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 3.51/1.53  tff(c_354, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.51/1.53  tff(c_30, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_358, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_30])).
% 3.51/1.53  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_356, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_32])).
% 3.51/1.53  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_367, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_34])).
% 3.51/1.53  tff(c_1083, plain, (![A_134, B_135]: (k1_tops_1(A_134, B_135)=k1_xboole_0 | ~v2_tops_1(B_135, A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.51/1.53  tff(c_1093, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1083])).
% 3.51/1.53  tff(c_1101, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_354, c_1093])).
% 3.51/1.53  tff(c_1392, plain, (![B_153, A_154, C_155]: (r1_tarski(B_153, k1_tops_1(A_154, C_155)) | ~r1_tarski(B_153, C_155) | ~v3_pre_topc(B_153, A_154) | ~m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.51/1.53  tff(c_1399, plain, (![B_153]: (r1_tarski(B_153, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_153, '#skF_2') | ~v3_pre_topc(B_153, '#skF_1') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1392])).
% 3.51/1.53  tff(c_1460, plain, (![B_160]: (r1_tarski(B_160, k1_xboole_0) | ~r1_tarski(B_160, '#skF_2') | ~v3_pre_topc(B_160, '#skF_1') | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1101, c_1399])).
% 3.51/1.53  tff(c_1467, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_367, c_1460])).
% 3.51/1.53  tff(c_1474, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_358, c_356, c_1467])).
% 3.51/1.53  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.51/1.53  tff(c_382, plain, (![A_80, C_81, B_82]: (r1_tarski(A_80, C_81) | ~r1_tarski(B_82, C_81) | ~r1_tarski(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.51/1.53  tff(c_394, plain, (![A_80, A_4]: (r1_tarski(A_80, A_4) | ~r1_tarski(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_382])).
% 3.51/1.53  tff(c_1501, plain, (![A_161]: (r1_tarski('#skF_3', A_161))), inference(resolution, [status(thm)], [c_1474, c_394])).
% 3.51/1.53  tff(c_6, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.51/1.53  tff(c_1539, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1501, c_6])).
% 3.51/1.53  tff(c_1562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_1539])).
% 3.51/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.53  
% 3.51/1.53  Inference rules
% 3.51/1.53  ----------------------
% 3.51/1.53  #Ref     : 0
% 3.51/1.53  #Sup     : 309
% 3.51/1.53  #Fact    : 0
% 3.51/1.53  #Define  : 0
% 3.51/1.53  #Split   : 11
% 3.51/1.53  #Chain   : 0
% 3.51/1.53  #Close   : 0
% 3.51/1.53  
% 3.51/1.53  Ordering : KBO
% 3.51/1.53  
% 3.51/1.53  Simplification rules
% 3.51/1.53  ----------------------
% 3.51/1.53  #Subsume      : 88
% 3.51/1.53  #Demod        : 238
% 3.51/1.53  #Tautology    : 114
% 3.51/1.53  #SimpNegUnit  : 13
% 3.51/1.53  #BackRed      : 7
% 3.51/1.53  
% 3.51/1.53  #Partial instantiations: 0
% 3.51/1.53  #Strategies tried      : 1
% 3.51/1.53  
% 3.51/1.53  Timing (in seconds)
% 3.51/1.53  ----------------------
% 3.51/1.54  Preprocessing        : 0.31
% 3.51/1.54  Parsing              : 0.16
% 3.51/1.54  CNF conversion       : 0.02
% 3.51/1.54  Main loop            : 0.47
% 3.51/1.54  Inferencing          : 0.17
% 3.51/1.54  Reduction            : 0.15
% 3.51/1.54  Demodulation         : 0.10
% 3.51/1.54  BG Simplification    : 0.02
% 3.51/1.54  Subsumption          : 0.10
% 3.51/1.54  Abstraction          : 0.02
% 3.51/1.54  MUC search           : 0.00
% 3.51/1.54  Cooper               : 0.00
% 3.51/1.54  Total                : 0.81
% 3.51/1.54  Index Insertion      : 0.00
% 3.51/1.54  Index Deletion       : 0.00
% 3.51/1.54  Index Matching       : 0.00
% 3.51/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
