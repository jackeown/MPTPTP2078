%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:08 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 143 expanded)
%              Number of leaves         :   26 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 613 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_20,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_73,plain,(
    ! [B_52,A_53,C_54] :
      ( r2_hidden(B_52,k1_tops_1(A_53,C_54))
      | ~ m1_connsp_2(C_54,A_53,B_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_52,u1_struct_0(A_53))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_77,plain,(
    ! [B_52] :
      ( r2_hidden(B_52,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_81,plain,(
    ! [B_52] :
      ( r2_hidden(B_52,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_77])).

tff(c_82,plain,(
    ! [B_52] :
      ( r2_hidden(B_52,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_81])).

tff(c_83,plain,(
    ! [B_55] :
      ( r2_hidden(B_55,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_55)
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_81])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [B_55] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_55)
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_88,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_51,plain,(
    ! [A_44,B_45] :
      ( v3_pre_topc(k1_tops_1(A_44,B_45),A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_56,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_53])).

tff(c_37,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_tops_1(A_41,B_42),B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_42,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_39])).

tff(c_57,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k1_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [D_37] :
      ( ~ r1_tarski(D_37,'#skF_4')
      | ~ v3_pre_topc(D_37,'#skF_2')
      | ~ m1_connsp_2(D_37,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_63,plain,(
    ! [B_47] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_47),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_47),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_47),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_57,c_18])).

tff(c_120,plain,(
    ! [B_63] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_63),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_63),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_63),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_63])).

tff(c_127,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_120])).

tff(c_133,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42,c_127])).

tff(c_134,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_133])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tops_1(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [B_59,A_60,C_61] :
      ( m1_connsp_2(B_59,A_60,C_61)
      | ~ r2_hidden(C_61,B_59)
      | ~ v3_pre_topc(B_59,A_60)
      | ~ m1_subset_1(C_61,u1_struct_0(A_60))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_102,plain,(
    ! [B_59] :
      ( m1_connsp_2(B_59,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_59)
      | ~ v3_pre_topc(B_59,'#skF_2')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_105,plain,(
    ! [B_59] :
      ( m1_connsp_2(B_59,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_59)
      | ~ v3_pre_topc(B_59,'#skF_2')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_102])).

tff(c_107,plain,(
    ! [B_62] :
      ( m1_connsp_2(B_62,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_62)
      | ~ v3_pre_topc(B_62,'#skF_2')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_105])).

tff(c_111,plain,(
    ! [B_6] :
      ( m1_connsp_2(k1_tops_1('#skF_2',B_6),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_6))
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_6),'#skF_2')
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_135,plain,(
    ! [B_64] :
      ( m1_connsp_2(k1_tops_1('#skF_2',B_64),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_64))
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_64),'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_111])).

tff(c_142,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_135])).

tff(c_148,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_142])).

tff(c_149,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_148])).

tff(c_152,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_149])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_152])).

tff(c_173,plain,(
    ! [B_66] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_66)
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_176,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:55:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.10/1.29  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.10/1.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.10/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.29  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.10/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.29  
% 2.10/1.31  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.10/1.31  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.10/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.10/1.31  tff(f_45, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.10/1.31  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.10/1.31  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.10/1.31  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.10/1.31  tff(c_20, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.10/1.31  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.10/1.31  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.10/1.31  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.10/1.31  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.10/1.31  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.10/1.31  tff(c_73, plain, (![B_52, A_53, C_54]: (r2_hidden(B_52, k1_tops_1(A_53, C_54)) | ~m1_connsp_2(C_54, A_53, B_52) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_52, u1_struct_0(A_53)) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.31  tff(c_77, plain, (![B_52]: (r2_hidden(B_52, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.10/1.31  tff(c_81, plain, (![B_52]: (r2_hidden(B_52, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_77])).
% 2.10/1.31  tff(c_82, plain, (![B_52]: (r2_hidden(B_52, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_81])).
% 2.10/1.31  tff(c_83, plain, (![B_55]: (r2_hidden(B_55, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_55) | ~m1_subset_1(B_55, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_81])).
% 2.10/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.31  tff(c_87, plain, (![B_55]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_55) | ~m1_subset_1(B_55, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_83, c_2])).
% 2.10/1.31  tff(c_88, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_87])).
% 2.10/1.31  tff(c_51, plain, (![A_44, B_45]: (v3_pre_topc(k1_tops_1(A_44, B_45), A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.31  tff(c_53, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.10/1.31  tff(c_56, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_53])).
% 2.10/1.31  tff(c_37, plain, (![A_41, B_42]: (r1_tarski(k1_tops_1(A_41, B_42), B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.31  tff(c_39, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_37])).
% 2.10/1.31  tff(c_42, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_39])).
% 2.10/1.31  tff(c_57, plain, (![A_46, B_47]: (m1_subset_1(k1_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.31  tff(c_18, plain, (![D_37]: (~r1_tarski(D_37, '#skF_4') | ~v3_pre_topc(D_37, '#skF_2') | ~m1_connsp_2(D_37, '#skF_2', '#skF_3') | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_37))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.10/1.31  tff(c_63, plain, (![B_47]: (~r1_tarski(k1_tops_1('#skF_2', B_47), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_47), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_47), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_57, c_18])).
% 2.10/1.31  tff(c_120, plain, (![B_63]: (~r1_tarski(k1_tops_1('#skF_2', B_63), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_63), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_63), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_63)) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_63])).
% 2.10/1.31  tff(c_127, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_120])).
% 2.10/1.31  tff(c_133, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_42, c_127])).
% 2.10/1.31  tff(c_134, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_88, c_133])).
% 2.10/1.31  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k1_tops_1(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.31  tff(c_100, plain, (![B_59, A_60, C_61]: (m1_connsp_2(B_59, A_60, C_61) | ~r2_hidden(C_61, B_59) | ~v3_pre_topc(B_59, A_60) | ~m1_subset_1(C_61, u1_struct_0(A_60)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.10/1.31  tff(c_102, plain, (![B_59]: (m1_connsp_2(B_59, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_59) | ~v3_pre_topc(B_59, '#skF_2') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_100])).
% 2.10/1.31  tff(c_105, plain, (![B_59]: (m1_connsp_2(B_59, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_59) | ~v3_pre_topc(B_59, '#skF_2') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_102])).
% 2.10/1.31  tff(c_107, plain, (![B_62]: (m1_connsp_2(B_62, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_62) | ~v3_pre_topc(B_62, '#skF_2') | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_105])).
% 2.10/1.31  tff(c_111, plain, (![B_6]: (m1_connsp_2(k1_tops_1('#skF_2', B_6), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_6)) | ~v3_pre_topc(k1_tops_1('#skF_2', B_6), '#skF_2') | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_107])).
% 2.10/1.31  tff(c_135, plain, (![B_64]: (m1_connsp_2(k1_tops_1('#skF_2', B_64), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_64)) | ~v3_pre_topc(k1_tops_1('#skF_2', B_64), '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_111])).
% 2.10/1.31  tff(c_142, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_135])).
% 2.10/1.31  tff(c_148, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_142])).
% 2.10/1.31  tff(c_149, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_134, c_148])).
% 2.10/1.31  tff(c_152, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_82, c_149])).
% 2.10/1.31  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_152])).
% 2.10/1.31  tff(c_173, plain, (![B_66]: (~m1_connsp_2('#skF_4', '#skF_2', B_66) | ~m1_subset_1(B_66, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_87])).
% 2.10/1.31  tff(c_176, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_173])).
% 2.10/1.31  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_176])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 23
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 2
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 2
% 2.10/1.31  #Demod        : 25
% 2.10/1.31  #Tautology    : 2
% 2.10/1.31  #SimpNegUnit  : 5
% 2.10/1.31  #BackRed      : 0
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.32
% 2.10/1.31  Parsing              : 0.18
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.19
% 2.10/1.31  Inferencing          : 0.08
% 2.10/1.31  Reduction            : 0.05
% 2.10/1.31  Demodulation         : 0.04
% 2.10/1.31  BG Simplification    : 0.01
% 2.10/1.31  Subsumption          : 0.03
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.32  MUC search           : 0.00
% 2.10/1.32  Cooper               : 0.00
% 2.10/1.32  Total                : 0.54
% 2.10/1.32  Index Insertion      : 0.00
% 2.10/1.32  Index Deletion       : 0.00
% 2.10/1.32  Index Matching       : 0.00
% 2.10/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
