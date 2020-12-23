%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1246+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:38 EST 2020

% Result     : Theorem 31.90s
% Output     : CNFRefutation 32.15s
% Verified   : 
% Statistics : Number of formulae       :  168 (1310 expanded)
%              Number of leaves         :   31 ( 467 expanded)
%              Depth                    :   28
%              Number of atoms          :  556 (6954 expanded)
%              Number of equality atoms :   16 (  94 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_tops_1(A,B))
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( ( v3_pre_topc(D,A)
                          & r2_hidden(C,D) )
                       => ( ~ r1_xboole_0(B,D)
                          & ~ r1_xboole_0(k3_subset_1(u1_struct_0(A),B),D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ~ ( v3_pre_topc(D,A)
                        & r2_hidden(C,D)
                        & r1_xboole_0(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_92157,plain,(
    ! [B_4500,A_4501,C_4502] :
      ( r1_xboole_0(B_4500,'#skF_3'(A_4501,B_4500,C_4502))
      | r2_hidden(C_4502,k2_pre_topc(A_4501,B_4500))
      | ~ m1_subset_1(C_4502,u1_struct_0(A_4501))
      | ~ m1_subset_1(B_4500,k1_zfmisc_1(u1_struct_0(A_4501)))
      | ~ l1_pre_topc(A_4501)
      | ~ v2_pre_topc(A_4501)
      | v2_struct_0(A_4501) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_92166,plain,(
    ! [C_4502] :
      ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_4502))
      | r2_hidden(C_4502,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4502,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_92157])).

tff(c_92175,plain,(
    ! [C_4502] :
      ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_4502))
      | r2_hidden(C_4502,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4502,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_92166])).

tff(c_92176,plain,(
    ! [C_4502] :
      ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_4502))
      | r2_hidden(C_4502,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4502,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_92175])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_17,B_29,C_35] :
      ( m1_subset_1('#skF_3'(A_17,B_29,C_35),k1_zfmisc_1(u1_struct_0(A_17)))
      | r2_hidden(C_35,k2_pre_topc(A_17,B_29))
      | ~ m1_subset_1(C_35,u1_struct_0(A_17))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98690,plain,(
    ! [A_4914,B_4915,C_4916] :
      ( r1_xboole_0(k3_subset_1(u1_struct_0(A_4914),B_4915),'#skF_3'(A_4914,k3_subset_1(u1_struct_0(A_4914),B_4915),C_4916))
      | r2_hidden(C_4916,k2_pre_topc(A_4914,k3_subset_1(u1_struct_0(A_4914),B_4915)))
      | ~ m1_subset_1(C_4916,u1_struct_0(A_4914))
      | ~ l1_pre_topc(A_4914)
      | ~ v2_pre_topc(A_4914)
      | v2_struct_0(A_4914)
      | ~ m1_subset_1(B_4915,k1_zfmisc_1(u1_struct_0(A_4914))) ) ),
    inference(resolution,[status(thm)],[c_24,c_92157])).

tff(c_68,plain,(
    ! [D_60] :
      ( r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),D_60)
      | ~ r2_hidden('#skF_6',D_60)
      | ~ v3_pre_topc(D_60,'#skF_4')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_91325,plain,(
    ! [D_60] :
      ( ~ r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),D_60)
      | ~ r2_hidden('#skF_6',D_60)
      | ~ v3_pre_topc(D_60,'#skF_4')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_68])).

tff(c_98696,plain,(
    ! [C_4916] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4916))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4916),'#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4916),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_4916,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_4916,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_98690,c_91325])).

tff(c_98700,plain,(
    ! [C_4916] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4916))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4916),'#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4916),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_4916,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_4916,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_44,c_98696])).

tff(c_98899,plain,(
    ! [C_4925] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4925))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4925),'#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4925),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_4925,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_4925,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_98700])).

tff(c_98903,plain,(
    ! [C_35] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_35))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_35),'#skF_4')
      | r2_hidden(C_35,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_98899])).

tff(c_98906,plain,(
    ! [C_35] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_35))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_35),'#skF_4')
      | r2_hidden(C_35,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_98903])).

tff(c_98907,plain,(
    ! [C_35] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_35))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_35),'#skF_4')
      | r2_hidden(C_35,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_98906])).

tff(c_99753,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_98907])).

tff(c_99756,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_24,c_99753])).

tff(c_99760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_99756])).

tff(c_99762,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_98907])).

tff(c_92439,plain,(
    ! [C_4525,A_4526,B_4527] :
      ( r2_hidden(C_4525,'#skF_3'(A_4526,B_4527,C_4525))
      | r2_hidden(C_4525,k2_pre_topc(A_4526,B_4527))
      | ~ m1_subset_1(C_4525,u1_struct_0(A_4526))
      | ~ m1_subset_1(B_4527,k1_zfmisc_1(u1_struct_0(A_4526)))
      | ~ l1_pre_topc(A_4526)
      | ~ v2_pre_topc(A_4526)
      | v2_struct_0(A_4526) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_92462,plain,(
    ! [C_4525,A_4526,B_13] :
      ( r2_hidden(C_4525,'#skF_3'(A_4526,k3_subset_1(u1_struct_0(A_4526),B_13),C_4525))
      | r2_hidden(C_4525,k2_pre_topc(A_4526,k3_subset_1(u1_struct_0(A_4526),B_13)))
      | ~ m1_subset_1(C_4525,u1_struct_0(A_4526))
      | ~ l1_pre_topc(A_4526)
      | ~ v2_pre_topc(A_4526)
      | v2_struct_0(A_4526)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_4526))) ) ),
    inference(resolution,[status(thm)],[c_24,c_92439])).

tff(c_117,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k2_pre_topc(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16] :
      ( k9_subset_1(A_14,B_15,C_16) = k3_xboole_0(B_15,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    ! [A_83,B_15,B_84] :
      ( k9_subset_1(u1_struct_0(A_83),B_15,k2_pre_topc(A_83,B_84)) = k3_xboole_0(B_15,k2_pre_topc(A_83,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_117,c_26])).

tff(c_99775,plain,(
    ! [B_15] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_15,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k3_xboole_0(B_15,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_99762,c_122])).

tff(c_100426,plain,(
    ! [B_4960] : k9_subset_1(u1_struct_0('#skF_4'),B_4960,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k3_xboole_0(B_4960,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_99775])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k9_subset_1(u1_struct_0(A_1),k2_pre_topc(A_1,B_3),k2_pre_topc(A_1,k3_subset_1(u1_struct_0(A_1),B_3))) = k2_tops_1(A_1,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100436,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_100426,c_2])).

tff(c_100453,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4','#skF_5'),k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_100436])).

tff(c_4,plain,(
    ! [D_9,A_4,B_5] :
      ( r2_hidden(D_9,k3_xboole_0(A_4,B_5))
      | ~ r2_hidden(D_9,B_5)
      | ~ r2_hidden(D_9,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_102691,plain,(
    ! [D_4969] :
      ( r2_hidden(D_4969,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_4969,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ r2_hidden(D_4969,k2_pre_topc('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100453,c_4])).

tff(c_102921,plain,(
    ! [C_4525] :
      ( r2_hidden(C_4525,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_4525,k2_pre_topc('#skF_4','#skF_5'))
      | r2_hidden(C_4525,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4525))
      | ~ m1_subset_1(C_4525,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_92462,c_102691])).

tff(c_103265,plain,(
    ! [C_4525] :
      ( r2_hidden(C_4525,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_4525,k2_pre_topc('#skF_4','#skF_5'))
      | r2_hidden(C_4525,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4525))
      | ~ m1_subset_1(C_4525,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_44,c_102921])).

tff(c_103749,plain,(
    ! [C_4988] :
      ( r2_hidden(C_4988,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_4988,k2_pre_topc('#skF_4','#skF_5'))
      | r2_hidden(C_4988,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4988))
      | ~ m1_subset_1(C_4988,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_103265])).

tff(c_91828,plain,(
    ! [A_4472,B_4473,C_4474] :
      ( v3_pre_topc('#skF_3'(A_4472,B_4473,C_4474),A_4472)
      | r2_hidden(C_4474,k2_pre_topc(A_4472,B_4473))
      | ~ m1_subset_1(C_4474,u1_struct_0(A_4472))
      | ~ m1_subset_1(B_4473,k1_zfmisc_1(u1_struct_0(A_4472)))
      | ~ l1_pre_topc(A_4472)
      | ~ v2_pre_topc(A_4472)
      | v2_struct_0(A_4472) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_95126,plain,(
    ! [A_4711,B_4712,C_4713] :
      ( v3_pre_topc('#skF_3'(A_4711,k3_subset_1(u1_struct_0(A_4711),B_4712),C_4713),A_4711)
      | r2_hidden(C_4713,k2_pre_topc(A_4711,k3_subset_1(u1_struct_0(A_4711),B_4712)))
      | ~ m1_subset_1(C_4713,u1_struct_0(A_4711))
      | ~ l1_pre_topc(A_4711)
      | ~ v2_pre_topc(A_4711)
      | v2_struct_0(A_4711)
      | ~ m1_subset_1(B_4712,k1_zfmisc_1(u1_struct_0(A_4711))) ) ),
    inference(resolution,[status(thm)],[c_24,c_91828])).

tff(c_92725,plain,(
    ! [A_4556,B_4557,C_4558] :
      ( m1_subset_1('#skF_3'(A_4556,B_4557,C_4558),k1_zfmisc_1(u1_struct_0(A_4556)))
      | r2_hidden(C_4558,k2_pre_topc(A_4556,B_4557))
      | ~ m1_subset_1(C_4558,u1_struct_0(A_4556))
      | ~ m1_subset_1(B_4557,k1_zfmisc_1(u1_struct_0(A_4556)))
      | ~ l1_pre_topc(A_4556)
      | ~ v2_pre_topc(A_4556)
      | v2_struct_0(A_4556) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_78,plain,(
    ! [D_60] :
      ( r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
      | ~ r1_xboole_0('#skF_5',D_60)
      | ~ r2_hidden('#skF_6',D_60)
      | ~ v3_pre_topc(D_60,'#skF_4')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_91167,plain,(
    ! [D_60] :
      ( ~ r1_xboole_0('#skF_5',D_60)
      | ~ r2_hidden('#skF_6',D_60)
      | ~ v3_pre_topc(D_60,'#skF_4')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78])).

tff(c_92741,plain,(
    ! [B_4557,C_4558] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',B_4557,C_4558))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',B_4557,C_4558))
      | ~ v3_pre_topc('#skF_3'('#skF_4',B_4557,C_4558),'#skF_4')
      | r2_hidden(C_4558,k2_pre_topc('#skF_4',B_4557))
      | ~ m1_subset_1(C_4558,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_4557,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92725,c_91167])).

tff(c_92758,plain,(
    ! [B_4557,C_4558] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',B_4557,C_4558))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',B_4557,C_4558))
      | ~ v3_pre_topc('#skF_3'('#skF_4',B_4557,C_4558),'#skF_4')
      | r2_hidden(C_4558,k2_pre_topc('#skF_4',B_4557))
      | ~ m1_subset_1(C_4558,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_4557,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_92741])).

tff(c_92759,plain,(
    ! [B_4557,C_4558] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',B_4557,C_4558))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',B_4557,C_4558))
      | ~ v3_pre_topc('#skF_3'('#skF_4',B_4557,C_4558),'#skF_4')
      | r2_hidden(C_4558,k2_pre_topc('#skF_4',B_4557))
      | ~ m1_subset_1(C_4558,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_4557,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_92758])).

tff(c_95129,plain,(
    ! [B_4712,C_4713] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712),C_4713))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712),C_4713))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),B_4712),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_4713,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712)))
      | ~ m1_subset_1(C_4713,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_4712,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_95126,c_92759])).

tff(c_95132,plain,(
    ! [B_4712,C_4713] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712),C_4713))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712),C_4713))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),B_4712),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_4713,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712)))
      | ~ m1_subset_1(C_4713,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_4712,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_95129])).

tff(c_95133,plain,(
    ! [B_4712,C_4713] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712),C_4713))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712),C_4713))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),B_4712),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_4713,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_4712)))
      | ~ m1_subset_1(C_4713,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_4712,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_95132])).

tff(c_103752,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_6'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_103749,c_95133])).

tff(c_103757,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_6'))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_99762,c_103752])).

tff(c_103758,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_6'))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_103757])).

tff(c_103763,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_103758])).

tff(c_103769,plain,
    ( r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_92176,c_103763])).

tff(c_103775,plain,(
    r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_103769])).

tff(c_92454,plain,(
    ! [C_4525] :
      ( r2_hidden(C_4525,'#skF_3'('#skF_4','#skF_5',C_4525))
      | r2_hidden(C_4525,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4525,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_92439])).

tff(c_92465,plain,(
    ! [C_4525] :
      ( r2_hidden(C_4525,'#skF_3'('#skF_4','#skF_5',C_4525))
      | r2_hidden(C_4525,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4525,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_92454])).

tff(c_92466,plain,(
    ! [C_4525] :
      ( r2_hidden(C_4525,'#skF_3'('#skF_4','#skF_5',C_4525))
      | r2_hidden(C_4525,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4525,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_92465])).

tff(c_103766,plain,
    ( r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_92466,c_103763])).

tff(c_103772,plain,(
    r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_103766])).

tff(c_91837,plain,(
    ! [C_4474] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5',C_4474),'#skF_4')
      | r2_hidden(C_4474,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4474,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_91828])).

tff(c_91846,plain,(
    ! [C_4474] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5',C_4474),'#skF_4')
      | r2_hidden(C_4474,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4474,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_91837])).

tff(c_91847,plain,(
    ! [C_4474] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5',C_4474),'#skF_4')
      | r2_hidden(C_4474,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4474,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_91846])).

tff(c_92846,plain,(
    ! [B_4570,C_4571] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4',B_4570,C_4571))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4',B_4570,C_4571))
      | ~ v3_pre_topc('#skF_3'('#skF_4',B_4570,C_4571),'#skF_4')
      | r2_hidden(C_4571,k2_pre_topc('#skF_4',B_4570))
      | ~ m1_subset_1(C_4571,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_4570,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_92758])).

tff(c_92850,plain,(
    ! [C_4474] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_4474))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5',C_4474))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_4474,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4474,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_91847,c_92846])).

tff(c_92856,plain,(
    ! [C_4474] :
      ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5',C_4474))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_4','#skF_5',C_4474))
      | r2_hidden(C_4474,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_4474,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_92850])).

tff(c_103779,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_103772,c_92856])).

tff(c_103786,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_103779])).

tff(c_103787,plain,(
    ~ r1_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_103763,c_103786])).

tff(c_103800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103775,c_103787])).

tff(c_103802,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_103758])).

tff(c_103266,plain,(
    ! [C_4525] :
      ( r2_hidden(C_4525,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_4525,k2_pre_topc('#skF_4','#skF_5'))
      | r2_hidden(C_4525,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4525))
      | ~ m1_subset_1(C_4525,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_103265])).

tff(c_91843,plain,(
    ! [A_4472,B_13,C_4474] :
      ( v3_pre_topc('#skF_3'(A_4472,k3_subset_1(u1_struct_0(A_4472),B_13),C_4474),A_4472)
      | r2_hidden(C_4474,k2_pre_topc(A_4472,k3_subset_1(u1_struct_0(A_4472),B_13)))
      | ~ m1_subset_1(C_4474,u1_struct_0(A_4472))
      | ~ l1_pre_topc(A_4472)
      | ~ v2_pre_topc(A_4472)
      | v2_struct_0(A_4472)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_4472))) ) ),
    inference(resolution,[status(thm)],[c_24,c_91828])).

tff(c_104598,plain,(
    ! [C_5040] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_5040))
      | ~ v3_pre_topc('#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_5040),'#skF_4')
      | r2_hidden(C_5040,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_5040,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_98907])).

tff(c_104605,plain,(
    ! [C_4474] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4474))
      | r2_hidden(C_4474,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_4474,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_91843,c_104598])).

tff(c_104609,plain,(
    ! [C_4474] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_4474))
      | r2_hidden(C_4474,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_4474,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_44,c_104605])).

tff(c_104611,plain,(
    ! [C_5041] :
      ( ~ r2_hidden('#skF_6','#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_5041))
      | r2_hidden(C_5041,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_5041,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_104609])).

tff(c_104614,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_103266,c_104611])).

tff(c_104619,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
    | r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_103802,c_104614])).

tff(c_104620,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_104619])).

tff(c_100963,plain,(
    ! [D_9] :
      ( r2_hidden(D_9,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_9,k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ r2_hidden(D_9,k2_pre_topc('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100453,c_4])).

tff(c_104623,plain,
    ( r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_104620,c_100963])).

tff(c_104628,plain,(
    r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103802,c_104623])).

tff(c_104630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_104628])).

tff(c_104631,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_104632,plain,(
    r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_104637,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104632,c_56])).

tff(c_54,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_104635,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104632,c_54])).

tff(c_110066,plain,(
    ! [C_5491,A_5492,B_5493] :
      ( r2_hidden(C_5491,'#skF_3'(A_5492,B_5493,C_5491))
      | r2_hidden(C_5491,k2_pre_topc(A_5492,B_5493))
      | ~ m1_subset_1(C_5491,u1_struct_0(A_5492))
      | ~ m1_subset_1(B_5493,k1_zfmisc_1(u1_struct_0(A_5492)))
      | ~ l1_pre_topc(A_5492)
      | ~ v2_pre_topc(A_5492)
      | v2_struct_0(A_5492) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_110077,plain,(
    ! [C_5491,A_5492,B_13] :
      ( r2_hidden(C_5491,'#skF_3'(A_5492,k3_subset_1(u1_struct_0(A_5492),B_13),C_5491))
      | r2_hidden(C_5491,k2_pre_topc(A_5492,k3_subset_1(u1_struct_0(A_5492),B_13)))
      | ~ m1_subset_1(C_5491,u1_struct_0(A_5492))
      | ~ l1_pre_topc(A_5492)
      | ~ v2_pre_topc(A_5492)
      | v2_struct_0(A_5492)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_5492))) ) ),
    inference(resolution,[status(thm)],[c_24,c_110066])).

tff(c_104673,plain,(
    ! [A_5058,B_5059] :
      ( m1_subset_1(k2_pre_topc(A_5058,B_5059),k1_zfmisc_1(u1_struct_0(A_5058)))
      | ~ m1_subset_1(B_5059,k1_zfmisc_1(u1_struct_0(A_5058)))
      | ~ l1_pre_topc(A_5058) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104949,plain,(
    ! [A_5098,B_5099,B_5100] :
      ( k9_subset_1(u1_struct_0(A_5098),B_5099,k2_pre_topc(A_5098,B_5100)) = k3_xboole_0(B_5099,k2_pre_topc(A_5098,B_5100))
      | ~ m1_subset_1(B_5100,k1_zfmisc_1(u1_struct_0(A_5098)))
      | ~ l1_pre_topc(A_5098) ) ),
    inference(resolution,[status(thm)],[c_104673,c_26])).

tff(c_107056,plain,(
    ! [A_5266,B_5267,B_5268] :
      ( k9_subset_1(u1_struct_0(A_5266),B_5267,k2_pre_topc(A_5266,k3_subset_1(u1_struct_0(A_5266),B_5268))) = k3_xboole_0(B_5267,k2_pre_topc(A_5266,k3_subset_1(u1_struct_0(A_5266),B_5268)))
      | ~ l1_pre_topc(A_5266)
      | ~ m1_subset_1(B_5268,k1_zfmisc_1(u1_struct_0(A_5266))) ) ),
    inference(resolution,[status(thm)],[c_24,c_104949])).

tff(c_108053,plain,(
    ! [A_5354,B_5355] :
      ( k3_xboole_0(k2_pre_topc(A_5354,B_5355),k2_pre_topc(A_5354,k3_subset_1(u1_struct_0(A_5354),B_5355))) = k2_tops_1(A_5354,B_5355)
      | ~ l1_pre_topc(A_5354)
      | ~ m1_subset_1(B_5355,k1_zfmisc_1(u1_struct_0(A_5354)))
      | ~ m1_subset_1(B_5355,k1_zfmisc_1(u1_struct_0(A_5354)))
      | ~ l1_pre_topc(A_5354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107056])).

tff(c_8,plain,(
    ! [D_9,A_4,B_5] :
      ( r2_hidden(D_9,A_4)
      | ~ r2_hidden(D_9,k3_xboole_0(A_4,B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_108287,plain,(
    ! [D_5356,A_5357,B_5358] :
      ( r2_hidden(D_5356,k2_pre_topc(A_5357,B_5358))
      | ~ r2_hidden(D_5356,k2_tops_1(A_5357,B_5358))
      | ~ l1_pre_topc(A_5357)
      | ~ m1_subset_1(B_5358,k1_zfmisc_1(u1_struct_0(A_5357)))
      | ~ m1_subset_1(B_5358,k1_zfmisc_1(u1_struct_0(A_5357)))
      | ~ l1_pre_topc(A_5357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108053,c_8])).

tff(c_108466,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_104632,c_108287])).

tff(c_108528,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_108466])).

tff(c_50,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_7')
    | r1_xboole_0('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_6',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_104650,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_7')
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104632,c_50])).

tff(c_104651,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_104650])).

tff(c_106399,plain,(
    ! [B_5229,D_5230,C_5231,A_5232] :
      ( ~ r1_xboole_0(B_5229,D_5230)
      | ~ r2_hidden(C_5231,D_5230)
      | ~ v3_pre_topc(D_5230,A_5232)
      | ~ m1_subset_1(D_5230,k1_zfmisc_1(u1_struct_0(A_5232)))
      | ~ r2_hidden(C_5231,k2_pre_topc(A_5232,B_5229))
      | ~ m1_subset_1(C_5231,u1_struct_0(A_5232))
      | ~ m1_subset_1(B_5229,k1_zfmisc_1(u1_struct_0(A_5232)))
      | ~ l1_pre_topc(A_5232)
      | ~ v2_pre_topc(A_5232)
      | v2_struct_0(A_5232) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_108534,plain,(
    ! [C_5359,A_5360] :
      ( ~ r2_hidden(C_5359,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_5360)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_5360)))
      | ~ r2_hidden(C_5359,k2_pre_topc(A_5360,'#skF_5'))
      | ~ m1_subset_1(C_5359,u1_struct_0(A_5360))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_5360)))
      | ~ l1_pre_topc(A_5360)
      | ~ v2_pre_topc(A_5360)
      | v2_struct_0(A_5360) ) ),
    inference(resolution,[status(thm)],[c_104651,c_106399])).

tff(c_108536,plain,(
    ! [C_5359] :
      ( ~ r2_hidden(C_5359,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ r2_hidden(C_5359,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_5359,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_104637,c_108534])).

tff(c_108539,plain,(
    ! [C_5359] :
      ( ~ r2_hidden(C_5359,'#skF_7')
      | ~ r2_hidden(C_5359,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_5359,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_104635,c_108536])).

tff(c_108541,plain,(
    ! [C_5361] :
      ( ~ r2_hidden(C_5361,'#skF_7')
      | ~ r2_hidden(C_5361,k2_pre_topc('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_5361,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_108539])).

tff(c_108544,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_108528,c_108541])).

tff(c_108793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_104631,c_108544])).

tff(c_108794,plain,(
    r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_104650])).

tff(c_110659,plain,(
    ! [B_5553,D_5554,C_5555,A_5556] :
      ( ~ r1_xboole_0(B_5553,D_5554)
      | ~ r2_hidden(C_5555,D_5554)
      | ~ v3_pre_topc(D_5554,A_5556)
      | ~ m1_subset_1(D_5554,k1_zfmisc_1(u1_struct_0(A_5556)))
      | ~ r2_hidden(C_5555,k2_pre_topc(A_5556,B_5553))
      | ~ m1_subset_1(C_5555,u1_struct_0(A_5556))
      | ~ m1_subset_1(B_5553,k1_zfmisc_1(u1_struct_0(A_5556)))
      | ~ l1_pre_topc(A_5556)
      | ~ v2_pre_topc(A_5556)
      | v2_struct_0(A_5556) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_117342,plain,(
    ! [C_5869,A_5870] :
      ( ~ r2_hidden(C_5869,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_5870)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_5870)))
      | ~ r2_hidden(C_5869,k2_pre_topc(A_5870,k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(C_5869,u1_struct_0(A_5870))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0(A_5870)))
      | ~ l1_pre_topc(A_5870)
      | ~ v2_pre_topc(A_5870)
      | v2_struct_0(A_5870) ) ),
    inference(resolution,[status(thm)],[c_108794,c_110659])).

tff(c_117489,plain,(
    ! [C_5491] :
      ( ~ r2_hidden(C_5491,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_5491,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_5491))
      | ~ m1_subset_1(C_5491,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_110077,c_117342])).

tff(c_117720,plain,(
    ! [C_5491] :
      ( ~ r2_hidden(C_5491,'#skF_7')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_5491,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_5491))
      | ~ m1_subset_1(C_5491,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_44,c_104637,c_104635,c_117489])).

tff(c_117721,plain,(
    ! [C_5491] :
      ( ~ r2_hidden(C_5491,'#skF_7')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(C_5491,'#skF_3'('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),C_5491))
      | ~ m1_subset_1(C_5491,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_117720])).

tff(c_117858,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_117721])).

tff(c_117861,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_24,c_117858])).

tff(c_117865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_117861])).

tff(c_117867,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_117721])).

tff(c_108837,plain,(
    ! [A_5375,B_5376] :
      ( m1_subset_1(k2_pre_topc(A_5375,B_5376),k1_zfmisc_1(u1_struct_0(A_5375)))
      | ~ m1_subset_1(B_5376,k1_zfmisc_1(u1_struct_0(A_5375)))
      | ~ l1_pre_topc(A_5375) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109093,plain,(
    ! [A_5410,B_5411,B_5412] :
      ( k9_subset_1(u1_struct_0(A_5410),B_5411,k2_pre_topc(A_5410,B_5412)) = k3_xboole_0(B_5411,k2_pre_topc(A_5410,B_5412))
      | ~ m1_subset_1(B_5412,k1_zfmisc_1(u1_struct_0(A_5410)))
      | ~ l1_pre_topc(A_5410) ) ),
    inference(resolution,[status(thm)],[c_108837,c_26])).

tff(c_110995,plain,(
    ! [A_5574,B_5575,B_5576] :
      ( k9_subset_1(u1_struct_0(A_5574),B_5575,k2_pre_topc(A_5574,k3_subset_1(u1_struct_0(A_5574),B_5576))) = k3_xboole_0(B_5575,k2_pre_topc(A_5574,k3_subset_1(u1_struct_0(A_5574),B_5576)))
      | ~ l1_pre_topc(A_5574)
      | ~ m1_subset_1(B_5576,k1_zfmisc_1(u1_struct_0(A_5574))) ) ),
    inference(resolution,[status(thm)],[c_24,c_109093])).

tff(c_112148,plain,(
    ! [A_5664,B_5665] :
      ( k3_xboole_0(k2_pre_topc(A_5664,B_5665),k2_pre_topc(A_5664,k3_subset_1(u1_struct_0(A_5664),B_5665))) = k2_tops_1(A_5664,B_5665)
      | ~ m1_subset_1(B_5665,k1_zfmisc_1(u1_struct_0(A_5664)))
      | ~ l1_pre_topc(A_5664)
      | ~ l1_pre_topc(A_5664)
      | ~ m1_subset_1(B_5665,k1_zfmisc_1(u1_struct_0(A_5664))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110995,c_2])).

tff(c_6,plain,(
    ! [D_9,B_5,A_4] :
      ( r2_hidden(D_9,B_5)
      | ~ r2_hidden(D_9,k3_xboole_0(A_4,B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112373,plain,(
    ! [D_9,A_5664,B_5665] :
      ( r2_hidden(D_9,k2_pre_topc(A_5664,k3_subset_1(u1_struct_0(A_5664),B_5665)))
      | ~ r2_hidden(D_9,k2_tops_1(A_5664,B_5665))
      | ~ m1_subset_1(B_5665,k1_zfmisc_1(u1_struct_0(A_5664)))
      | ~ l1_pre_topc(A_5664)
      | ~ l1_pre_topc(A_5664)
      | ~ m1_subset_1(B_5665,k1_zfmisc_1(u1_struct_0(A_5664))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112148,c_6])).

tff(c_117492,plain,(
    ! [D_9] :
      ( ~ r2_hidden(D_9,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_9,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(D_9,k2_tops_1('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_112373,c_117342])).

tff(c_117724,plain,(
    ! [D_9] :
      ( ~ r2_hidden(D_9,'#skF_7')
      | ~ m1_subset_1(D_9,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(D_9,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_46,c_104637,c_104635,c_117492])).

tff(c_117725,plain,(
    ! [D_9] :
      ( ~ r2_hidden(D_9,'#skF_7')
      | ~ m1_subset_1(D_9,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(D_9,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_117724])).

tff(c_117857,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_117725])).

tff(c_117908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117867,c_117857])).

tff(c_118737,plain,(
    ! [D_5878] :
      ( ~ r2_hidden(D_5878,'#skF_7')
      | ~ m1_subset_1(D_5878,u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_5878,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_117725])).

tff(c_119160,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_104632,c_118737])).

tff(c_119269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_104631,c_119160])).

%------------------------------------------------------------------------------
