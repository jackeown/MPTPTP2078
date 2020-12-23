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
% DateTime   : Thu Dec  3 10:21:40 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 250 expanded)
%              Number of leaves         :   32 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  126 ( 594 expanded)
%              Number of equality atoms :   30 ( 137 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_51,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_36])).

tff(c_133,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(A_57,B_58,C_59) = k3_xboole_0(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    ! [B_58] : k9_subset_1(k2_struct_0('#skF_2'),B_58,'#skF_3') = k3_xboole_0(B_58,'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_133])).

tff(c_28,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_149,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_52])).

tff(c_30,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,A_52)
      | ~ r2_hidden(C_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_180,plain,(
    ! [A_67,B_68,A_69] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_69)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_69))
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_192,plain,(
    ! [A_70,A_71] :
      ( ~ m1_subset_1(A_70,k1_zfmisc_1(A_71))
      | r1_tarski(A_70,A_71) ) ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_203,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_192])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_208,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_203,c_8])).

tff(c_34,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_326,plain,(
    ! [A_79,B_80] :
      ( k2_pre_topc(A_79,B_80) = k2_struct_0(A_79)
      | ~ v1_tops_1(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_332,plain,(
    ! [B_80] :
      ( k2_pre_topc('#skF_2',B_80) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_80,'#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_326])).

tff(c_346,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_2',B_83) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_332])).

tff(c_355,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_346])).

tff(c_362,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_355])).

tff(c_159,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k2_pre_topc(A_62,B_63),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_164,plain,(
    ! [B_63] :
      ( m1_subset_1(k2_pre_topc('#skF_2',B_63),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_159])).

tff(c_167,plain,(
    ! [B_63] :
      ( m1_subset_1(k2_pre_topc('#skF_2',B_63),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_51,c_164])).

tff(c_372,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_167])).

tff(c_383,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_372])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( k9_subset_1(A_14,B_15,C_16) = k3_xboole_0(B_15,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_402,plain,(
    ! [B_15] : k9_subset_1(k2_struct_0('#skF_2'),B_15,k2_struct_0('#skF_2')) = k3_xboole_0(B_15,k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_383,c_14])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_405,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_pre_topc(A_84,k9_subset_1(u1_struct_0(A_84),B_85,k2_pre_topc(A_84,C_86))) = k2_pre_topc(A_84,k9_subset_1(u1_struct_0(A_84),B_85,C_86))
      | ~ v3_pre_topc(B_85,A_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_437,plain,(
    ! [B_85,C_86] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_85,k2_pre_topc('#skF_2',C_86))) = k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_85,C_86))
      | ~ v3_pre_topc(B_85,'#skF_2')
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_405])).

tff(c_1451,plain,(
    ! [B_128,C_129] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_128,k2_pre_topc('#skF_2',C_129))) = k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_128,C_129))
      | ~ v3_pre_topc(B_128,'#skF_2')
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_51,c_51,c_51,c_437])).

tff(c_1496,plain,(
    ! [B_128] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_128,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_128,'#skF_3'))
      | ~ v3_pre_topc(B_128,'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_1451])).

tff(c_3742,plain,(
    ! [B_284] :
      ( k2_pre_topc('#skF_2',k3_xboole_0(B_284,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0(B_284,'#skF_3'))
      | ~ v3_pre_topc(B_284,'#skF_2')
      | ~ m1_subset_1(B_284,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_402,c_139,c_1496])).

tff(c_3754,plain,
    ( k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3742])).

tff(c_3764,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_208,c_3754])).

tff(c_3766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_3764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:59:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.31  
% 6.34/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.31  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.34/2.31  
% 6.34/2.31  %Foreground sorts:
% 6.34/2.31  
% 6.34/2.31  
% 6.34/2.31  %Background operators:
% 6.34/2.31  
% 6.34/2.31  
% 6.34/2.31  %Foreground operators:
% 6.34/2.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.34/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.34/2.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.34/2.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.34/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.34/2.31  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 6.34/2.31  tff('#skF_2', type, '#skF_2': $i).
% 6.34/2.31  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.34/2.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.34/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.31  tff('#skF_4', type, '#skF_4': $i).
% 6.34/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.34/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.34/2.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.34/2.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.34/2.31  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.34/2.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.34/2.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.34/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.31  
% 6.34/2.32  tff(f_103, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 6.34/2.32  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.34/2.32  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.34/2.32  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.34/2.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.34/2.32  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.34/2.32  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.34/2.32  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 6.34/2.32  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.34/2.32  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 6.34/2.32  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.34/2.32  tff(c_20, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.34/2.32  tff(c_42, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.34/2.32  tff(c_47, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_20, c_42])).
% 6.34/2.32  tff(c_51, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_47])).
% 6.34/2.32  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.34/2.32  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_36])).
% 6.34/2.32  tff(c_133, plain, (![A_57, B_58, C_59]: (k9_subset_1(A_57, B_58, C_59)=k3_xboole_0(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.32  tff(c_139, plain, (![B_58]: (k9_subset_1(k2_struct_0('#skF_2'), B_58, '#skF_3')=k3_xboole_0(B_58, '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_133])).
% 6.34/2.32  tff(c_28, plain, (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.34/2.32  tff(c_52, plain, (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 6.34/2.32  tff(c_149, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_52])).
% 6.34/2.32  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.34/2.32  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.34/2.32  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_32])).
% 6.34/2.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.34/2.32  tff(c_100, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, A_52) | ~r2_hidden(C_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.34/2.32  tff(c_180, plain, (![A_67, B_68, A_69]: (r2_hidden('#skF_1'(A_67, B_68), A_69) | ~m1_subset_1(A_67, k1_zfmisc_1(A_69)) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_6, c_100])).
% 6.34/2.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.34/2.32  tff(c_192, plain, (![A_70, A_71]: (~m1_subset_1(A_70, k1_zfmisc_1(A_71)) | r1_tarski(A_70, A_71))), inference(resolution, [status(thm)], [c_180, c_4])).
% 6.34/2.32  tff(c_203, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_192])).
% 6.34/2.32  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.34/2.32  tff(c_208, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_203, c_8])).
% 6.34/2.32  tff(c_34, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.34/2.32  tff(c_326, plain, (![A_79, B_80]: (k2_pre_topc(A_79, B_80)=k2_struct_0(A_79) | ~v1_tops_1(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.34/2.32  tff(c_332, plain, (![B_80]: (k2_pre_topc('#skF_2', B_80)=k2_struct_0('#skF_2') | ~v1_tops_1(B_80, '#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_326])).
% 6.34/2.32  tff(c_346, plain, (![B_83]: (k2_pre_topc('#skF_2', B_83)=k2_struct_0('#skF_2') | ~v1_tops_1(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_332])).
% 6.34/2.32  tff(c_355, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_346])).
% 6.34/2.32  tff(c_362, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_355])).
% 6.34/2.32  tff(c_159, plain, (![A_62, B_63]: (m1_subset_1(k2_pre_topc(A_62, B_63), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.34/2.32  tff(c_164, plain, (![B_63]: (m1_subset_1(k2_pre_topc('#skF_2', B_63), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_159])).
% 6.34/2.32  tff(c_167, plain, (![B_63]: (m1_subset_1(k2_pre_topc('#skF_2', B_63), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_51, c_164])).
% 6.34/2.32  tff(c_372, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_362, c_167])).
% 6.34/2.32  tff(c_383, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_372])).
% 6.34/2.32  tff(c_14, plain, (![A_14, B_15, C_16]: (k9_subset_1(A_14, B_15, C_16)=k3_xboole_0(B_15, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.32  tff(c_402, plain, (![B_15]: (k9_subset_1(k2_struct_0('#skF_2'), B_15, k2_struct_0('#skF_2'))=k3_xboole_0(B_15, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_383, c_14])).
% 6.34/2.32  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.34/2.32  tff(c_405, plain, (![A_84, B_85, C_86]: (k2_pre_topc(A_84, k9_subset_1(u1_struct_0(A_84), B_85, k2_pre_topc(A_84, C_86)))=k2_pre_topc(A_84, k9_subset_1(u1_struct_0(A_84), B_85, C_86)) | ~v3_pre_topc(B_85, A_84) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.34/2.32  tff(c_437, plain, (![B_85, C_86]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_85, k2_pre_topc('#skF_2', C_86)))=k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_85, C_86)) | ~v3_pre_topc(B_85, '#skF_2') | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_405])).
% 6.34/2.32  tff(c_1451, plain, (![B_128, C_129]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_128, k2_pre_topc('#skF_2', C_129)))=k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_128, C_129)) | ~v3_pre_topc(B_128, '#skF_2') | ~m1_subset_1(C_129, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_128, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_51, c_51, c_51, c_437])).
% 6.34/2.32  tff(c_1496, plain, (![B_128]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_128, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_128, '#skF_3')) | ~v3_pre_topc(B_128, '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_128, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_362, c_1451])).
% 6.34/2.32  tff(c_3742, plain, (![B_284]: (k2_pre_topc('#skF_2', k3_xboole_0(B_284, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0(B_284, '#skF_3')) | ~v3_pre_topc(B_284, '#skF_2') | ~m1_subset_1(B_284, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_402, c_139, c_1496])).
% 6.34/2.32  tff(c_3754, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_3742])).
% 6.34/2.32  tff(c_3764, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_208, c_3754])).
% 6.34/2.32  tff(c_3766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_3764])).
% 6.34/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.32  
% 6.34/2.32  Inference rules
% 6.34/2.32  ----------------------
% 6.34/2.32  #Ref     : 0
% 6.34/2.32  #Sup     : 930
% 6.34/2.32  #Fact    : 0
% 6.34/2.32  #Define  : 0
% 6.34/2.32  #Split   : 8
% 6.34/2.32  #Chain   : 0
% 6.34/2.32  #Close   : 0
% 6.34/2.32  
% 6.34/2.32  Ordering : KBO
% 6.34/2.32  
% 6.34/2.32  Simplification rules
% 6.34/2.32  ----------------------
% 6.34/2.32  #Subsume      : 178
% 6.34/2.32  #Demod        : 1991
% 6.34/2.32  #Tautology    : 373
% 6.34/2.32  #SimpNegUnit  : 8
% 6.34/2.32  #BackRed      : 4
% 6.34/2.32  
% 6.34/2.32  #Partial instantiations: 0
% 6.34/2.32  #Strategies tried      : 1
% 6.34/2.32  
% 6.34/2.32  Timing (in seconds)
% 6.34/2.32  ----------------------
% 6.34/2.33  Preprocessing        : 0.35
% 6.34/2.33  Parsing              : 0.19
% 6.34/2.33  CNF conversion       : 0.03
% 6.34/2.33  Main loop            : 1.16
% 6.34/2.33  Inferencing          : 0.37
% 6.34/2.33  Reduction            : 0.43
% 6.34/2.33  Demodulation         : 0.33
% 6.34/2.33  BG Simplification    : 0.05
% 6.34/2.33  Subsumption          : 0.23
% 6.34/2.33  Abstraction          : 0.06
% 6.34/2.33  MUC search           : 0.00
% 6.34/2.33  Cooper               : 0.00
% 6.34/2.33  Total                : 1.55
% 6.34/2.33  Index Insertion      : 0.00
% 6.34/2.33  Index Deletion       : 0.00
% 6.34/2.33  Index Matching       : 0.00
% 6.34/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
